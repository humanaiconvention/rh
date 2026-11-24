"""Benign host-isolation/resource controls. No RH/Lean proof verdict."""
import errno
import json
import os
import pathlib
import socket
import sys
import time

case = sys.argv[1]
result = {"case": case, "uid": os.getuid(), "pid": os.getpid()}
if case == "isolation":
    assert os.getuid() != 0
    assert "RH_GAUSS_FORBIDDEN_SENTINEL" not in os.environ, "ENV_LEAK"
    assert not pathlib.Path(sys.argv[2]).exists(), "HOST_FILE_LEAK"
    assert os.stat("/proc/self/ns/net").st_ino != int(sys.argv[3]), "NETWORK_NAMESPACE_UNCHANGED"
    assert not pathlib.Path("/home/runner").exists()
    assert not pathlib.Path("/run/credentials").exists()
    assert not pathlib.Path("/work/.git").exists()
    try:
        pathlib.Path("/work/read-only.txt").write_text("must not be possible")
    except OSError as e:
        assert e.errno in (errno.EROFS, errno.EACCES, errno.EPERM), str(e)
        result["readonly_rejection"] = e.errno
    else:
        raise AssertionError("read-only input writable")
    sock = socket.socket()
    sock.settimeout(0.5)
    try:
        sock.connect(("1.1.1.1", 443))
    except OSError as e:
        assert e.errno == errno.ENETUNREACH, str(e)
        result["network_rejection"] = e.errno
    else:
        raise AssertionError("network unexpectedly available")
    finally:
        sock.close()
    result["environment_keys"] = sorted(os.environ)
    result["status"] = "PASS"
    pathlib.Path("/out/isolation.json").write_text(json.dumps(result, sort_keys=True))
elif case == "pids":
    children = []
    try:
        for _ in range(8):
            pid = os.fork()
            if pid == 0:
                time.sleep(2)
                os._exit(0)
            children.append(pid)
    except OSError as e:
        assert e.errno == errno.EAGAIN, str(e)
        result.update(status="EXPECTED_KERNEL_REJECTION", errno=e.errno,
                      children_started=len(children))
    else:
        raise AssertionError("eight forks fit the four-task cap")
    finally:
        for pid in children:
            os.kill(pid, 9)
        for pid in children:
            os.waitpid(pid, 0)
    pathlib.Path("/out/pids.json").write_text(json.dumps(result, sort_keys=True))
elif case == "memory":
    blocks = []
    for _ in range(1024):
        blocks.append(bytearray(1024 * 1024))
    raise AssertionError("memory control did not kill excessive allocation")
elif case == "timeout":
    time.sleep(30)
    raise AssertionError("timeout control returned normally")
else:
    raise AssertionError("unknown fixture")
print(json.dumps(result, sort_keys=True), flush=True)
