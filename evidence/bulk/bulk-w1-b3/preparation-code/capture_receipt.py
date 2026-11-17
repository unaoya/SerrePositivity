"""Integrity receipts for an independently completed side of a native capture."""
from pathlib import Path
import hashlib,json

def valid_capture(path,signature,side,modules):
 path=Path(path);receipt=path.with_suffix('.capture.json')
 try:
  r=json.loads(receipt.read_text())
  return r['signature']==signature and r['side']==side and r['modules']==modules and r['sha256']==hashlib.sha256(path.read_bytes()).hexdigest()
 except (OSError,ValueError,KeyError,TypeError):return False

def save_capture(path,signature,side,modules,seconds=0):
 path=Path(path);d=json.loads(path.read_text());assert set(d['modules'])==set(modules)
 receipt=path.with_suffix('.capture.json');temporary=receipt.with_suffix('.tmp');temporary.write_text(json.dumps({'signature':signature,'side':side,'modules':modules,'seconds':seconds,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()},indent=2));temporary.replace(receipt)
