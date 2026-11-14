"""Schedule two independent captures; choose one under memory pressure or for scripts."""
import subprocess,re,concurrent.futures

def available_memory_bytes():
 try:
  s=subprocess.check_output(['vm_stat'],text=True);size=int(re.search(r'page size of (\d+) bytes',s)[1]);pages=0
  for label in ['free','inactive','speculative']:
   m=re.search(r'Pages '+label+r':\s+(\d+)',s)
   if m:pages+=int(m[1])
  return pages*size
 except (OSError,ValueError,TypeError,subprocess.SubprocessError):return 0

def run_independent_captures(specs,capture):
 available=available_memory_bytes();workers=2 if available>=20*1024**3 and all(all(m.startswith('SerrePositivity.') for m in spec[1]) for spec in specs) else 1
 with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:results=list(pool.map(capture,specs))
 return results,workers,available
