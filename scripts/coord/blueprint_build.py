"""ブループリントのビルド（調整役）：blueprint の Lean を 10 分の塊で建て、lake exe vbp build でサイトを作る。鍵 coord、待っているレーンに譲る。
使い方：nohup python3 scripts/coord/blueprint_build.py > <出力> 2>&1 &　最後に「site rc 0」。その後 rsync でサイトを差し替えて blueprint/scripts/style_site.py をかける。"""
import subprocess,time,re,sys,pathlib
MAINP=pathlib.Path(__file__).resolve().parents[2]; B=MAINP/'blueprint'
MAIN=str(MAINP)
LOCK=str(MAINP/'scripts/refactor/with_build_lock.sh')
def yield_to_lanes():
    t0=time.time()
    while time.time()-t0<2100:
        st=subprocess.run(['zsh',LOCK,'--status'],cwd=MAIN,capture_output=True,text=True).stdout
        m=re.search(r'queue \(day order\): (\d+)',st); w=int(m.group(1)) if m else 0
        if w==0: return
        time.sleep(30)
def run(cmd,t):
    yield_to_lanes()
    p=subprocess.run(['zsh',LOCK,'--class','coord','--wait','7200','--','gtimeout','--kill-after=10s',f'{t}s']+cmd,cwd=B,capture_output=True,text=True)
    return p.returncode,p.stdout+p.stderr
n=0
while True:
    n+=1; rc,out=run(['lake','build','SerreBlueprint'],600)
    print(time.strftime('%H:%M'),'blueprint-lean chunk',n,'rc',rc,flush=True)
    if rc==0: break
    if rc not in (124,137): print(out[-4000:]); sys.exit(1)
rc,out=run(['lake','exe','vbp','build'],1500); print(time.strftime('%H:%M'),'site rc',rc); print(out[-3000:])
