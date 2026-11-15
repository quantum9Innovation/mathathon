"""Rebuild the vector mathematical illustrations used by the slide source."""
from pathlib import Path
import math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle, FancyArrowPatch

OUT=Path(__file__).resolve().parent/'assets';OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'serif','font.size':11,'mathtext.fontset':'cm',
 'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
BLUE='#24558a';RED='#a64d31';GRAY='#676767'
def save(fig,name):
    fig.savefig(OUT/(name+'.pdf'),bbox_inches='tight',pad_inches=.05)
    plt.close(fig)
def graph(ax,pos,edges,labels=None,colors=None,width=1.5):
    for u,v in edges:
        ax.plot([pos[u][0],pos[v][0]],[pos[u][1],pos[v][1]],color='#666666',lw=width,zorder=1)
    for u,(x,y) in pos.items():
        ax.scatter([x],[y],s=145,c=[(colors or {}).get(u,'white')],edgecolors='black',linewidths=1,zorder=3)
        if labels is not None: ax.text(x,y,str(labels[u]),ha='center',va='center',fontsize=10,zorder=4)
    xs=[x for x,y in pos.values()];ys=[y for x,y in pos.values()]
    pad=max(.35,.13*max(max(xs)-min(xs),max(ys)-min(ys)))
    ax.set_xlim(min(xs)-pad,max(xs)+pad);ax.set_ylim(min(ys)-pad,max(ys)+pad)
    ax.set_aspect('equal');ax.axis('off')

fig,axs=plt.subplots(1,4,figsize=(11,2.4))
for ax,kind in zip(axs,['Path $P_5$','Cycle $C_5$','Complete $K_4$','Star $K_{1,4}$']):
    if kind.startswith('Path'):
        pos={i:(i,0) for i in range(5)};edges=[(i,i+1) for i in range(4)]
    elif kind.startswith('Cycle'):
        pos={i:(math.cos(2*math.pi*i/5),math.sin(2*math.pi*i/5)) for i in range(5)};edges=[(i,(i+1)%5) for i in range(5)]
    elif kind.startswith('Complete'):
        pos={i:(math.cos(math.pi/4+i*math.pi/2),math.sin(math.pi/4+i*math.pi/2)) for i in range(4)};edges=[(i,j) for i in range(4) for j in range(i)]
    else:
        pos={0:(0,0),1:(1,0),2:(-1,0),3:(0,1),4:(0,-1)};edges=[(0,i) for i in range(1,5)]
    graph(ax,pos,edges);ax.set_title(kind,pad=12)
save(fig,'graph-families')

fig,ax=plt.subplots(figsize=(5.5,1.4));graph(ax,{0:(0,0),1:(1,0),2:(2,0)},[(0,1),(1,2)],{0:'1',1:'2',2:'3'});save(fig,'path-three')

fig,axs=plt.subplots(1,3,figsize=(9,2.4))
vals=[[1,1,1,1],[1,-1,1,-1],[1,0,-1,0]]
for ax,v,t in zip(axs,vals,[r'$\lambda=2$: constant',r'$\lambda=-2$: alternating',r'$\lambda=0$: cancellation']):
    pos={0:(0,1),1:(1,1),2:(1,0),3:(0,0)}
    colors={i:('#dce8f4' if z>0 else '#f4e2db' if z<0 else 'white') for i,z in enumerate(v)}
    graph(ax,pos,[(0,1),(1,2),(2,3),(3,0)],dict(enumerate(v)),colors);ax.set_title(t,pad=7)
save(fig,'cycle-modes')

pos={0:(-3,1),1:(-3,-1),2:(-1.5,1),3:(-1.5,-1),4:(1.5,-1),5:(1.5,1),6:(3,-1),7:(3,1)}
edges=[(i,j) for i in range(4) for j in range(i)]+[(i,j) for i in range(4,8) for j in range(4,i)]+[(3,4)]
A=np.zeros((8,8))
for i,j in edges:A[i,j]=A[j,i]=1
L=np.diag(A.sum(axis=1))-A;eig,vec=np.linalg.eigh(L);v=vec[:,1]
if v[0]<0:v=-v
fig,axs=plt.subplots(1,2,figsize=(10,3),gridspec_kw={'width_ratios':[1.3,1]})
graph(axs[0],pos,edges,colors={i:('#dce8f4' if i<4 else '#f4e2db') for i in range(8)})
axs[0].text(0,-1.7,'one connecting edge',ha='center',fontsize=10)
axs[1].axhline(0,color='black',lw=.7);axs[1].bar(np.arange(1,9),v,color=[BLUE]*4+[RED]*4,width=.65)
axs[1].set_xticks(range(1,9));axs[1].set_xlabel('vertex');axs[1].set_ylabel('Fiedler-vector coordinate');axs[1].set_ylim(-.5,.5)
fig.tight_layout();save(fig,'spectral-cut')

fig,axs=plt.subplots(1,2,figsize=(8,2.8))
for ax,cells,title in zip(axs,[[(0,0),(2,2)],[(0,0),(0,2)]],['Distinct rows and columns','One common row']):
    for i in range(6):ax.plot([0,5],[i,i],color='#aaaaaa',lw=.6);ax.plot([i,i],[0,5],color='#aaaaaa',lw=.6)
    for r,c in cells:ax.scatter(c+.5,4.5-r,s=65,color=BLUE if title.startswith('Distinct') else RED)
    ax.set_title(title,pad=10);ax.set_aspect('equal');ax.axis('off')
save(fig,'requested-cells')

fig,axs=plt.subplots(1,2,figsize=(7.5,3))
for ax,n in zip(axs,[6,4]):
    for r in range(n):
        for c in range(n):
            fill='#eeeeee' if n==6 and (r in [1,4] or c in [0,3]) else 'white'
            ax.add_patch(Rectangle((c,n-r-1),1,1,fc=fill,ec='#999999',lw=.6))
    if n==6:
        for r,c in [(1,0),(4,3)]:ax.scatter(c+.5,n-r-.5,color=RED,s=60)
    ax.set_xlim(-.1,n+.1);ax.set_ylim(-.1,n+.1);ax.set_aspect('equal');ax.axis('off')
    ax.set_title('$N=6$, two matches fixed' if n==6 else 'Uniform permutation on 4 rows',fontsize=11,pad=10)
save(fig,'depleted-matrix')

fig,ax=plt.subplots(figsize=(8,3))
for side,x in [('L',0),('R',4)]:
    groups=[3,3] if side=='L' else [2,2,2]
    idx=0
    for k,num in enumerate(groups):
        ys=[]
        for q in range(num):
            y=5-idx;ys.append(y);ax.scatter(x,y,s=45,color=BLUE if side=='L' else RED,zorder=3);idx+=1
        ax.text(x+(-.35 if side=='L' else .35),sum(ys)/num,side+str(k+1),ha='right' if side=='L' else 'left',va='center')
perm=[3,0,4,1,5,2]
for i,j in enumerate(perm):ax.plot([0,4],[5-i,5-j],color='#aaaaaa',lw=.8)
ax.text(0,6,'2 vertices, degree 3',ha='center');ax.text(4,6,'3 vertices, degree 2',ha='center');ax.text(2,-.8,'6 half-edges on each side',ha='center');ax.axis('off');ax.set_ylim(-1,6.5)
save(fig,'biregular-matching')

fig,ax=plt.subplots(figsize=(8,3.5));pos={2*i+j:(2*i,1.5*j) for i in range(4) for j in range(2)}
edges=[]
for i in range(4):
    for j in range(i+1,4):
        swap=True  # Bipartite double cover: every base edge swaps the two sheets.
        edges += [(2*i+t,2*j+(1-t if swap else t)) for t in range(2)]
colors={2*i+j:['#dce8f4','#f4e2db','#e4eddf','#ece2f0'][i] for i in range(4) for j in range(2)}
graph(ax,pos,edges,colors=colors,width=1)
for i in range(4):ax.text(2*i,-.65,'fiber '+str(i+1),ha='center')
ax.text(3,2.25,'An example of a 2-lift of $K_4$',ha='center');save(fig,'lift-example')

fig,ax=plt.subplots(figsize=(8,3));pos={0:(-2,1.4),1:(2,1.4),2:(2,-1.4),3:(-2,-1.4),4:(-.9,.6),5:(.9,.6),6:(.9,-.6),7:(-.9,-.6)}
edges=[(i,(i//4)*4+(i+1)%4) for i in range(8)]+[(0,4),(1,5),(2,6),(3,7)]
graph(ax,pos,edges,colors={i:('#dce8f4' if i<4 else '#f4e2db') for i in range(8)})
ax.text(0,1.95,'Group A: outer cycle; group B: inner cycle',ha='center',fontsize=10);save(fig,'two-groups')

fig,ax=plt.subplots(figsize=(7,2.6));N=np.logspace(1,3,100)
ax.loglog(N,4/N**2,color=GRAY,label='ambiguity leading term $4/N^2$');ax.loglog(N,2/N**2,color=BLUE,label='optimal error leading term $2/N^2$')
ax.set_xlabel('one group size $N$');ax.set_ylabel('asymptotic leading term');ax.legend(frameon=False,fontsize=9);ax.grid(alpha=.2,which='major');fig.tight_layout();save(fig,'ambiguity-rates')
print('Rebuilt',len(list(OUT.glob('*.pdf'))),'vector figures.')
