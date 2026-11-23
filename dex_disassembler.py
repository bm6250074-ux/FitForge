import struct,glob,sys,os
sys.path.insert(0,'/home/claude/work')
from dexcls import read_uleb
L={}
for r,ops in [(1,[0x00,0x01,0x04,0x07,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x11,0x12,0x1d,0x1e,0x21,0x27,0x28]),
 (2,[0x02,0x05,0x08,0x13,0x15,0x16,0x19,0x1a,0x1c,0x1f,0x20,0x22,0x23,0x29]),
 (3,[0x03,0x06,0x09,0x14,0x17,0x1b,0x24,0x25,0x26,0x2a,0x2b,0x2c])]:
    for o in ops:L[o]=r
for o in range(0x2d,0x3e):L[o]=2
for o in range(0x3e,0x44):L[o]=1
for o in range(0x44,0x6e):L[o]=2
for o in range(0x6e,0x73):L[o]=3
L[0x73]=1
for o in range(0x74,0x79):L[o]=3
for o in (0x79,0x7a):L[o]=1
for o in range(0x7b,0x90):L[o]=1
for o in range(0x90,0xb0):L[o]=2
for o in range(0xb0,0xd0):L[o]=1
for o in range(0xd0,0xe3):L[o]=2
for o in range(0xe3,0xfa):L[o]=1
L[0xfa]=4;L[0xfb]=4;L[0xfc]=3;L[0xfd]=3;L[0xfe]=2;L[0xff]=2
L[0x18]=5
class Dex:
    def __init__(s,path):
        b=s.b=open(path,'rb').read()
        sc,so=struct.unpack_from('<II',b,56);tc,to=struct.unpack_from('<II',b,64)
        pc,po=struct.unpack_from('<II',b,72);fc,fo=struct.unpack_from('<II',b,80)
        s.mc,s.mo=struct.unpack_from('<II',b,88);s.cc,s.co=struct.unpack_from('<II',b,96)
        s.strs=[]
        for i in range(sc):
            off=struct.unpack_from('<I',b,so+4*i)[0];l,o=read_uleb(b,off)
            s.strs.append(b[o:b.index(b'\0',o)].decode('utf8','replace'))
        s.types=[struct.unpack_from('<I',b,to+4*i)[0] for i in range(tc)]
        s.po=po;s.fo=fo
    def T(s,i):return s.strs[s.types[i]]
    def M(s,i):
        cl,pr,nm=struct.unpack_from('<HHI',s.b,s.mo+8*i)
        return s.T(cl)+'.'+s.strs[nm]
    def F(s,i):
        cl,ty,nm=struct.unpack_from('<HHI',s.b,s.fo+8*i)
        return s.T(cl)+'.'+s.strs[nm]
    def methods(s,cname):
        b=s.b
        for i in range(s.cc):
            ci,af,sup,ifs,sf,ann,cd,sv=struct.unpack_from('<8I',b,s.co+32*i)
            if s.T(ci)!=cname or not cd: continue
            o=cd
            sfn,o=read_uleb(b,o);ifn,o=read_uleb(b,o);dm,o=read_uleb(b,o);vm,o=read_uleb(b,o)
            for _ in range(sfn+ifn):_,o=read_uleb(b,o);_,o=read_uleb(b,o)
            for n in (dm,vm):
                mid=0
                for _ in range(n):
                    d,o=read_uleb(b,o);mid+=d;_,o=read_uleb(b,o);code,o=read_uleb(b,o)
                    if code: yield s.M(mid),code
    def dis(s,code):
        b=s.b
        regs,ins_,outs,tries,dbg,isz=struct.unpack_from('<HHHHII',b,code)
        ins=struct.unpack_from('<%dH'%isz,b,code+16)
        out=[];p=0
        while p<isz:
            w=ins[p];op=w&0xff
            if w in(0x100,0x200,0x300) and p+1<isz:
                if w==0x100:ln=ins[p+1]*2+4
                elif w==0x200:ln=ins[p+1]*4+2
                else:
                    wd=ins[p+1];sz=ins[p+2]|(ins[p+3]<<16);ln=(sz*wd+1)//2+4
                    data=b[code+16+2*(p+4):code+16+2*(p+4)+sz*wd]
                    out.append('  array-data w=%d %s'%(wd,data.hex()))
                p+=ln;continue
            n=L.get(op,1)
            a=(w>>8)&0xf;bb=(w>>12)&0xf;aa=w>>8
            if op==0x12:
                v=bb if bb<8 else bb-16;out.append('  const/4 v%d, %d'%(a,v))
            elif op==0x13:out.append('  const/16 v%d, %d'%(aa,struct.unpack('<h',struct.pack('<H',ins[p+1]))[0]))
            elif op==0x14:out.append('  const v%d, %d'%(aa,struct.unpack('<i',struct.pack('<I',ins[p+1]|ins[p+2]<<16))[0]))
            elif op==0x15:out.append('  const/high16 v%d, 0x%x'%(aa,ins[p+1]<<16))
            elif op==0x1a:out.append('  const-string v%d, %r'%(aa,s.strs[ins[p+1]][:80]))
            elif op==0x1b:out.append('  const-string v%d, %r'%(aa,s.strs[ins[p+1]|ins[p+2]<<16][:80]))
            elif op in range(0x6e,0x73) or op in range(0x74,0x79):
                out.append('  invoke %s (%s)'%(s.M(ins[p+1]),','.join('v%d'%x for x in ([ins[p+2]&0xf,(ins[p+2]>>4)&0xf,(ins[p+2]>>8)&0xf,(ins[p+2]>>12)&0xf,a][:(w>>12)] ) )) if op<0x74 else '  invoke/range %s v%d..'%(s.M(ins[p+1]),ins[p+2]))
            elif 0x52<=op<=0x5f or 0x60<=op<=0x6d:
                out.append('  %s v%d,%s %s'%('iget/iput' if op<0x60 else 'sget/sput',a if op<0x60 else aa,'',s.F(ins[p+1])))
            elif 0x4b<=op<=0x51:out.append('  aput v%d -> v%d[v%d]'%(aa,ins[p+1]&0xff,ins[p+1]>>8))
            elif op in (0x0e,0x0f,0x10,0x11):out.append('  return v%d'%aa)
            elif op in (0x01,0x07,0x0d,0x0a,0x0b,0x0c):out.append('  move/res op%02x v%d,v%d'%(op,a,bb))
            elif 0x90<=op<=0x9a:
                nm=['add','sub','mul','div','rem','and','or','xor','shl','shr','ushr'][op-0x90];out.append('  %s-int v%d,v%d,v%d'%(nm,aa,ins[p+1]&0xff,ins[p+1]>>8))
            elif 0xb0<=op<=0xba:
                nm=['add','sub','mul','div','rem','and','or','xor','shl','shr','ushr'][op-0xb0];out.append('  %s-int/2addr v%d,v%d'%(nm,a,bb))
            elif 0xd0<=op<=0xd7:
                nm=['add','rsub','mul','div','rem','and','or','xor'][op-0xd0];out.append('  %s-int/lit16 v%d,v%d,%d'%(nm,a,bb,struct.unpack('<h',struct.pack('<H',ins[p+1]))[0]))
            elif 0xd8<=op<=0xe2:
                nm=['add','rsub','mul','div','rem','and','or','xor','shl','shr','ushr'][op-0xd8];out.append('  %s-int/lit8 v%d,v%d,%d'%(nm,aa,ins[p+1]&0xff,struct.unpack('<b',bytes([ins[p+1]>>8]))[0]))
            elif op==0x21:out.append('  array-length v%d,v%d'%(a,bb))
            elif op==0x22:out.append('  new-instance v%d %s'%(aa,s.T(ins[p+1])))
            elif op==0x23:out.append('  new-array v%d,v%d %s'%(a,bb,s.T(ins[p+1])))
            elif op==0x28 or op==0x29 or op==0x2a:out.append('  goto')
            elif 0x32<=op<=0x3d:out.append('  if op%02x'%op)
            elif 0xd0<=op<=0xe2 or 0x90<=op<=0xaf or 0xb0<=op<=0xcf:out.append('  arith op%02x'%op)
            p+=n
        return out
if __name__=='__main__':
    cls=sys.argv[1];pat=sys.argv[2:] 
    os.chdir('/home/claude/work/fitpro_2.11.1_APKPure/base')
    for f in sorted(glob.glob('classes*.dex')):
        d=Dex(f)
        for m,code in d.methods(cls):
            nm=m.split('.',1)[1]
            if not pat or any(x in nm for x in pat):
                print('##',f,nm);print('\n'.join(d.dis(code)))
