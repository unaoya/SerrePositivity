"""Source-only named-declaration hints; native ownership capture is authoritative."""
import re
def declarations(text,path):
    # Strip nested Lean block comments, then scan named declarations and scope commands.
    clean=[];depth=0;i=0
    while i<len(text):
        if text.startswith('/-',i):depth+=1;i+=2;continue
        if depth and text.startswith('-/',i):depth-=1;i+=2;continue
        if depth:
            if text[i]=='\n':clean.append('\n')
            i+=1;continue
        if text.startswith('--',i):
            j=text.find('\n',i);i=len(text) if j<0 else j;continue
        clean.append(text[i]);i+=1
    stack=[];ns='';out=[]
    for lineno,line in enumerate(''.join(clean).splitlines(),1):
        line=line.strip()
        m=re.match(r'namespace\s+(\S+)',line)
        if m:
            stack.append(ns);n=m[1];ns=n.removeprefix('_root_.') if n.startswith('_root_.') else '.'.join(filter(None,[ns,n]));continue
        if re.match(r'(?:noncomputable\s+)?section(?:\s|$)',line):stack.append(ns);continue
        if re.match(r'end(?:\s|$)',line):
            if stack:ns=stack.pop()
            continue
        line=re.sub(r'^@\[[^]]*\]\s*','',line)
        if re.match(r'(?:public\s+)?private\s',line):continue
        m=re.match(r'(?:(?:public|noncomputable|protected|unsafe|partial)\s+)*(?:def|abbrev|lemma|theorem|opaque|axiom|structure|class|inductive|instance)\s+([^\s(:{]+)',line)
        if not m:continue
        name=m[1]
        if name in ['where',':=']:continue
        fq=name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(filter(None,[ns,name]))
        out.append((fq,path,lineno))
    return out
