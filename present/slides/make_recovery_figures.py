"""Exact graph illustrations for the elementary recovery slide sequence."""
from pathlib import Path
from itertools import product
import json, math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Circle, Rectangle

OUT=Path(__file__).resolve().parent/'assets'; OUT.mkdir(exist_ok=True)
BLUE='#285f9b'; ORANGE='#b65a30'; GRAY='#777777'; RED='#a22a2a'
plt.rcParams.update({'font.family':'serif','font.size':13,'mathtext.fontset':'cm','pdf.fonttype':42})
POS={0:(0,2),1:(-2,-1.35),2:(2,-1.35),3:(0,.85),4:(-.75,-.45),5:(.75,-.45)}
EDGES=[(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,3),(1,4),(2,5)]
ADJ={i:{v if u==i else u for u,v in EDGES if i in (u,v)} for i in range(6)}
TRUE={0,1,2}; BAD={0,1,3}

def save(fig,name):
    fig.savefig(OUT/(name+'.pdf'),bbox_inches='tight',pad_inches=.10)
    plt.close(fig)

def draw(ax,group=None,focus=None,marks=False,title=None,foot=None):
    for u,v in EDGES:
        color='#999999';lw=1.5
        if focus is not None and focus in (u,v) and group is not None:
            other=v if u==focus else u
            color=BLUE if (other in group)==(focus in group) else ORANGE;lw=3.4
        ax.plot([POS[u][0],POS[v][0]],[POS[u][1],POS[v][1]],color=color,lw=lw,zorder=1)
    for i,(x,y) in POS.items():
        fill='white' if group is None else ('#d9e8f6' if i in group else '#f5e0d5')
        ax.scatter([x],[y],s=660 if i==focus else 530,c=[fill],edgecolors='black',linewidths=2.4 if i==focus else 1.2,zorder=3)
        label=str(int(i in group)) if marks else str(i+1)
        ax.text(x,y,label,ha='center',va='center',fontsize=16,zorder=4)
        if marks:
            dx,dy={0:(.35,.15),1:(-.3,-.32),2:(.3,-.32),3:(.33,.05),4:(-.32,.1),5:(.32,.1)}[i]
            ax.text(x+dx,y+dy,str(i+1),ha='center',va='center',color=GRAY,fontsize=10)
    if title:ax.set_title(title,pad=12,fontsize=14)
    if foot:ax.text(0,-2.03,foot,ha='center',va='top',fontsize=12)
    ax.set_xlim(-2.7,2.7);ax.set_ylim(-2.25,2.7)
    ax.set_aspect('equal');ax.axis('off')

for name,group,focus,marks,title,foot in [
 ('recovery-uncolored',None,None,False,None,None),
 ('recovery-colored',TRUE,None,False,None,'Blue: group A.   Orange: group B.'),
 ('recovery-local-count',TRUE,1,False,None,'At vertex 2: two blue neighbors and one orange neighbor.'),
 ('recovery-wrong',BAD,1,False,None,'At vertex 2: one same-group neighbor and two across.'),
 ('recovery-marks',TRUE,1,True,None,'Large numbers: group marks.   Small numbers: vertex names.'),
]:
    fig,ax=plt.subplots(figsize=(6,4.5));draw(ax,group,focus,marks,title,foot);save(fig,name)

# All modular candidates, computed directly from the actual six-vertex graph.
def mod_ok(x):return all((sum(x[w] for w in ADJ[v])-x[v]-1)%3==0 for v in range(6))
def int_ok(x):return set(x)<={0,1} and all(sum(x[w] for w in ADJ[v])==1+x[v] for v in range(6))
candidates=[x for x in product(range(3),repeat=6) if mod_ok(x)]
valid=[x for x in candidates if int_ok(x)]
assert len(candidates)==9 and set(valid)=={(1,1,1,0,0,0),(0,0,0,1,1,1)}
assert sum(w in BAD for w in ADJ[1])==1
assert all(sum(w in TRUE for w in ADJ[v])==1+int(v in TRUE) for v in range(6))
fig,ax=plt.subplots(figsize=(10,3.0));ax.set_xlim(0,9.6);ax.set_ylim(-.1,3.0);ax.axis('off')
for j,x in enumerate(candidates):
    col=j%3;row=2-j//3;left=.10+col*3.2;bottom=.10+row*.9
    good=x in valid
    ax.add_patch(FancyBboxPatch((left,bottom),2.9,.66,boxstyle='round,pad=.06',fc='#edf4fb' if good else 'white',ec=BLUE if good else '#b7b7b7',lw=1.7 if good else 1))
    for k,val in enumerate(x):ax.text(left+.37+k*.42,bottom+.34,str(val),ha='center',va='center',fontfamily='monospace',fontsize=18,color=RED if val==2 else 'black')
ax.text(4.8,2.95,'Nine solutions of the clock equations for this graph and this rule',ha='center',va='bottom',fontsize=13)
save(fig,'recovery-nine-candidates')

fig,axs=plt.subplots(1,2,figsize=(9,3.8))
draw(axs[0],TRUE,title='111000');draw(axs[1],set(range(6))-TRUE,title='000111')
fig.text(.5,.03,'Swapping the two colors gives the same division into groups.',ha='center',fontsize=13)
save(fig,'recovery-same-partition')

fig,axs=plt.subplots(1,2,figsize=(9,3.8))
draw(axs[0],None,title='One group: every vertex has 3 neighbors inside')
draw(axs[1],TRUE,title='Two groups: 2 neighbors inside, 1 across')
save(fig,'recovery-coarse-fine')

fig,ax=plt.subplots(figsize=(11.5,2.1));ax.set_xlim(0,11.5);ax.set_ylim(0,2.1);ax.axis('off')
steps=['Try a\ncount rule','Write\nequations','Solve on a\nsmall clock','Check ordinary\nneighbor counts','Keep the most\ndetailed answer']
for j,label in enumerate(steps):
    left=.10+j*2.3
    ax.add_patch(Rectangle((left,.5),1.98,1.10,fc='white',ec=BLUE,lw=1.5))
    ax.text(left+.99,1.05,label,ha='center',va='center',fontsize=12)
    if j<4:ax.annotate('',xy=(left+2.28,1.05),xytext=(left+2.01,1.05),arrowprops={'arrowstyle':'->','lw':1.6,'color':'black'})
save(fig,'recovery-workflow')

fig,ax=plt.subplots(figsize=(6,2.8));ax.set_aspect('equal');ax.axis('off');cx,cy=0,0;r=1
for i in range(3):
    t=math.pi/2-2*math.pi*i/3;x,y=cx+r*math.cos(t),cy+r*math.sin(t)
    ax.add_patch(Circle((x,y),.22,fc='#edf4fb',ec=BLUE,lw=1.5));ax.text(x,y,str(i),ha='center',va='center',fontsize=19)
    t2=math.pi/2-2*math.pi*((i+1)%3)/3
    start=(cx+.87*r*math.cos(t-.20),cy+.87*r*math.sin(t-.20));end=(cx+.87*r*math.cos(t2+.20),cy+.87*r*math.sin(t2+.20))
    ax.add_patch(FancyArrowPatch(start,end,connectionstyle='arc3,rad=-.25',arrowstyle='->',mutation_scale=16,lw=1.5,color=GRAY))
ax.text(2.0,.4,r'$2+1=0$',fontsize=21);ax.text(2.0,-.35,r'$2+2=1$',fontsize=21)
ax.set_xlim(-1.3,4.0);ax.set_ylim(-1.0,1.4);save(fig,'recovery-clock')

fig,ax=plt.subplots(figsize=(8,2.5));ax.axis('off');ax.set_xlim(0,8);ax.set_ylim(0,2.5)
for x,y in [(0.5,.5),(4.3,.1)]:
    scale=1 if x<1 else 2
    ax.add_patch(Rectangle((x,y),scale,scale,ec=BLUE,fc='#edf4fb',lw=1.5))
    if scale==2:
        ax.plot([x+1,x+1],[y,y+2],c=BLUE,lw=1);ax.plot([x,x+2],[y+1,y+1],c=BLUE,lw=1)
    ax.text(x+scale/2,y+scale/2,'one unit' if scale==1 else 'four units',ha='center',va='center',fontsize=13)
ax.annotate('',xy=(3.9,1.1),xytext=(2.0,1.1),arrowprops={'arrowstyle':'->','lw':1.8})
ax.text(2.95,1.45,'double graph size',ha='center',fontsize=12)
ax.text(1.0,.1,r'$n^2$',ha='center',fontsize=17);ax.text(5.3,2.25,r'$(2n)^2=4n^2$',ha='center',fontsize=17)
save(fig,'recovery-work-bound')

report={'graph':'triangular prism','edges_1_based':[[u+1,v+1] for u,v in EDGES],
 'fixed_rule':'two neighbors in own group; one across','modular_candidate_count':len(candidates),
 'valid_markings':[''.join(map(str,x)) for x in valid],
 'unordered_valid_partition_count':1,
 'bad_partition_same_neighbors_at_vertex_2':sum(w in BAD for w in ADJ[1]),
 'scope':'Finite illustrative check for the fixed rule only; not uniqueness over unknown count tables.'}
(OUT/'recovery-exact-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
