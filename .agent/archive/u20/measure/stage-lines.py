#!/usr/bin/env python3
# Per-stage added Lean code lines (comments + blank lines excluded, codeLines-like) per arm commit.
import subprocess, sys, re
def code_lines(text):
    n=0; depth=0
    for line in text.splitlines():
        s=line.strip(); i=0; code=False
        while i < len(s):
            if depth>0:
                if s.startswith('-/',i): depth-=1; i+=2; continue
                if s.startswith('/-',i): depth+=1; i+=2; continue
                i+=1; continue
            if s.startswith('--',i): break
            if s.startswith('/-',i): depth+=1; i+=2; continue
            if not s[i].isspace(): code=True
            i+=1
        if code: n+=1
    return n
wt=sys.argv[1]; base=sys.argv[2]
revs=subprocess.run(['git','-C',wt,'rev-list','--reverse',f'{base}..HEAD'],capture_output=True,text=True).stdout.split()
total=0
for r in revs:
    subj=subprocess.run(['git','-C',wt,'log','-1','--format=%s',r],capture_output=True,text=True).stdout.strip()
    files=subprocess.run(['git','-C',wt,'diff','--name-only','--diff-filter=AM',f'{r}~1',r,'--','*.lean'],capture_output=True,text=True).stdout.split()
    added=0; deleted=0
    for f in files:
        new=subprocess.run(['git','-C',wt,'show',f'{r}:{f}'],capture_output=True,text=True).stdout
        old=subprocess.run(['git','-C',wt,'show',f'{r}~1:{f}'],capture_output=True,text=True)
        old=old.stdout if old.returncode==0 else ''
        cn,co=code_lines(new),code_lines(old)
        added+=max(cn-co,0); deleted+=max(co-cn,0)
    total+=added
    print(f"{r[:7]}\t+{added}\t-{deleted}\t{subj}")
print(f"total\t+{total}")
