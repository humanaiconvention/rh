"""Acquire a vendor-pinned compiler in the ephemeral worker; execute nothing."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import urllib.request

assert re.fullmatch(r"[0-9]+", os.environ["GITHUB_RUN_ID"])
pins = json.loads(Path(__file__).with_name("PINS.json").read_text())
asset = pins["future_linux_asset"]
assert asset["sha256"] == "2e1bbb832870bb81b7131cb70b13aec2cc7ed9f22e2bdbb236b86076ae20382d"
assert shutil.disk_usage(os.environ["RUNNER_TEMP"]).free >= 8 * 1024**3, "disk gate"
prior = Path(os.environ["RUNNER_TEMP"]) / "rh-gauss437-results" / "REPORT.json"
report = json.loads(prior.read_text())
assert report["infrastructure_controls"] == "PASS"
assert report["worker_commit"] == os.environ["GITHUB_SHA"]
assert all(x["empty"] for x in report["cleanup"])
archive = Path(os.environ["RUNNER_TEMP"]) / asset["name"]
assert not archive.exists(), "no acquisition retry/old archive reuse"
started = time.monotonic()
digest = hashlib.sha256()
size = 0
with urllib.request.urlopen(asset["url"], timeout=30) as source, archive.open("xb") as out:
    while True:
        block = source.read(1024 * 1024)
        if not block:
            break
        size += len(block)
        assert size <= asset["size"], "unexpected archive size"
        assert time.monotonic() - started < 240, "input-acquisition deadline"
        digest.update(block)
        out.write(block)
assert size == asset["size"] and digest.hexdigest() == asset["sha256"], "vendor digest mismatch"
dest = Path("/tmp") / ("rh-gauss437-" + os.environ["GITHUB_RUN_ID"]) / "lean"
dest.mkdir(mode=0o755, exist_ok=False)
subprocess.run(["tar", "--zstd", "-xf", str(archive), "--strip-components=1", "-C", str(dest)],
               check=True, timeout=90)
receipt = {"stage": "LINUX_COMPILER_ACQUISITION_NOT_EXECUTION",
           "worker_commit": os.environ["GITHUB_SHA"], "source_revision_expected": pins["lean_revision"],
           "url": asset["url"], "vendor_API_sha256": asset["sha256"],
           "observed_archive_sha256": digest.hexdigest(), "bytes": size,
           "independent_vendor_attestation": "NOT_CLAIMED", "executed": False,
           "elapsed": time.monotonic() - started}
(prior.parent / "LEAN-ACQUISITION.json").write_text(json.dumps(receipt, indent=2, sort_keys=True))
print(json.dumps(receipt, sort_keys=True), flush=True)
