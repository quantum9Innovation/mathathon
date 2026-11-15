"""Assemble the revised teaching deck from preserved and new editable frames."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
old = (ROOT/'present/slides/revisions/2026-11-15-first-revision/slides.tex').read_text()
frames = re.findall(r'\\begin\{frame\}.*?\\end\{frame\}', old, re.S)

preamble = r'''\documentclass[aspectratio=169,11pt]{beamer}
\usepackage{amsmath,amssymb,graphicx,tikz}
\usetikzlibrary{arrows.meta,positioning}
\usetheme{Madrid}
\usefonttheme{serif}
\setbeamertemplate{navigation symbols}{}
\setbeamertemplate{blocks}[default]
\setbeamertemplate{theorems}[numbered]
\setbeamersize{text margin left=8mm,text margin right=8mm}
\setlength{\parskip}{.35em}
\newcommand{\one}{\mathbf 1}
\newcommand{\E}{\mathbb E}
\newcommand{\F}{\mathbb F}
\newcommand{\Prob}{\mathbb P}
\newcommand{\R}{\mathbb R}
\newcommand{\Afig}[2][]{\includegraphics[#1]{present/slides/assets/#2.pdf}}
\newcommand{\source}[1]{\par\vfill{\scriptsize\color{black!65}#1}}
\title[Spectral graph theory]{Spectral graph theory\\and exact recovery of hidden groups}
\subtitle{Graph examples, random pairings, and a recovery theorem}
\author[Farfan--Shum--Venkatesh]{Angelo Farfan \and Carlos Shum \and Ananth Venkatesh}
\institute[Monadic Burrito]{Monadic Burrito}
\date{November 15, 2026}
\hypersetup{pdftitle={Spectral graph theory and exact recovery of hidden groups},pdfauthor={Angelo Farfan, Carlos Shum, Ananth Venkatesh}}
\pdfstringdefDisableCommands{\def\translate#1{#1}}
\begin{document}
'''

route = r'''\begin{frame}{Plan of the talk}
\tableofcontents[hideallsubsections,sections={1-4}]
\medskip
We start with small graphs and work toward one question:
\begin{center}\emph{Can exact neighbor counts reveal groups whose labels were erased?}\end{center}
\source{Elementary background: Pan, Nie and Wang, \href{https://math.mit.edu/research/highschool/primes/circle/documents/2025/Brian-Nathan-Daniel-Final.pdf}{\emph{An Introduction to Spectral Graph Theory}} (MIT PRIMES Circle, 2025).}
\end{frame}
'''

matching = r'''\begin{frame}{A matching: no vertex is used twice}
\begin{definition}
A \emph{matching} is a selection of edges with no shared endpoint.
Equivalently, each vertex has at most one selected partner.
\end{definition}
\begin{columns}[T]
\column{.48\textwidth}\centering
\Afig[height=2.9cm,width=\linewidth,keepaspectratio]{teaching-matching}
\column{.48\textwidth}\centering
\Afig[height=2.9cm,width=\linewidth,keepaspectratio]{teaching-nonmatching}
\end{columns}
\small Colored edges are selected. Dashed gray edges remain available.
\end{frame}

\begin{frame}{A perfect matching gives everyone exactly one partner}
\begin{definition}
A matching is \emph{perfect} if every vertex belongs to a selected edge.
\end{definition}
\begin{columns}[c]
\column{.49\textwidth}\centering
\Afig[height=3.0cm,width=\linewidth,keepaspectratio]{teaching-perfect}
\column{.47\textwidth}
There are six vertices and three selected edges.

Every vertex is covered exactly once.

By contrast, the previous two-edge matching left two vertices unpaired.
\end{columns}
\end{frame}

\begin{frame}{A bipartite graph has two sides}
\begin{definition}
The vertices can be divided into a left side and a right side so that
every edge joins the two sides.
\end{definition}
\begin{columns}[c]
\column{.48\textwidth}\centering
\begin{tikzpicture}[scale=.78,vertex/.style={circle,draw,fill=white,inner sep=2pt}]
\node[vertex] (a) at (0,1) {$a$};
\node[vertex] (b) at (0,-1) {$b$};
\node[vertex] (x) at (3,1.5) {$1$};
\node[vertex] (y) at (3,0) {$2$};
\node[vertex] (z) at (3,-1.5) {$3$};
\foreach \u in {a,b} {\foreach \v in {x,y,z} {\draw (\u)--(\v);}}
\node at (0,2.2) {left};\node at (3,2.2) {right};
\end{tikzpicture}
\column{.47\textwidth}
No edges lie within a side.

This example is $K_{2,3}$: all possible cross-side edges are present.

A triangle cannot be split into two sides in this way.
\end{columns}
\end{frame}
'''

pairings = r'''\begin{frame}{Pairings between two equal sides are permutations}
\begin{center}\Afig[height=3.55cm,width=.94\textwidth,keepaspectratio]{teaching-bipartite-perfect}\end{center}
A perfect matching pairs every left vertex with a different right vertex.
This one-to-one assignment is a \emph{bijection}, or permutation of the right labels.

The matrix records a $1$ for each selected pair: exactly one $1$ per row and column.
\end{frame}

\begin{frame}{What does a uniformly random perfect matching mean?}
Suppose every left vertex may pair with every right vertex.
For three vertices on each side:
\[
 3\text{ choices for the first partner}\;\times\;
 2\text{ for the next}\;\times\;1=6.
\]
\begin{block}{Uniform means equally likely}
Each of the six complete pairings has probability $1/6$.
For $N$ vertices on each side there are $N!$ pairings, each with probability $1/N!$.
\end{block}
Once a right vertex is paired, no other left vertex may use it.
That restriction makes different matching entries dependent.
\end{frame}

\begin{frame}{A lift replaces one edge by a perfect matching}
\begin{center}\Afig[height=3.55cm,width=.95\textwidth,keepaspectratio]{teaching-elementary-lift}\end{center}
A \emph{fiber} is the group of copies of one original vertex.
For each original edge, pair its two fibers by a perfect matching.
Choose these matchings independently for different original edges.
\end{frame}

\begin{frame}{Example: lifting a four-vertex complete graph}
\begin{center}\Afig[height=3.45cm,width=.83\textwidth,keepaspectratio]{lift-example}\end{center}
Each fiber has two copies. Each original edge contributes one matching.
Every vertex still has three neighbors, one in each other fiber.
\end{frame}
'''

centering = r'''\begin{frame}{Centering means subtracting the average}
For a random pairing, $M_{ij}$ is $1$ if $i$ is paired with $j$, and $0$ otherwise.
Each of the $N$ possible partners is equally likely, so $\E M_{ij}=1/N$.

Here $\E$ means the average over all possible random pairings.
\begin{example}[A row when $N=3$]
\[
 (0,1,0)\quad\longmapsto\quad
 \left(-\tfrac13,\tfrac23,-\tfrac13\right).
\]
Subtracting the average $1/3$ from every entry makes the row sum zero.
\end{example}
Positive and negative terms can now cancel when we add them.
\end{frame}

\begin{frame}{Prior work and the Proposition 28 question}
\begin{itemize}
\item Bordenave's Proposition 28 bounds products of centered matching entries
in the proof of the random-lift spectral theorem.
\item Brito--Dumitriu--Harris use the same ingredient for bipartite biregular graphs.
\item Collins--Nagatsu give related undepleted recurrences and diagonal leading terms.
\end{itemize}
\begin{block}{Our first contribution}
An intuitive proof: expose compatible pairs, retain the exact remaining
row sum, and use its cancellation before taking absolute values.
\end{block}
The report gives the full product estimate and proof.
\end{frame}

\begin{frame}{After fixing some pairs, the rest are still uniformly paired}
\begin{center}\Afig[height=3.15cm,width=.80\textwidth,keepaspectratio]{depleted-matrix}\end{center}
Two known pairs use two rows and two columns. Four rows and columns remain.

Every perfect matching between these remaining rows and columns is still equally likely.
\begin{block}{Why this helps}
The smaller matching has an exact row sum. Keeping that identity preserves
cancellation that an early absolute-value bound would lose.
\end{block}
\end{frame}

\begin{frame}{How the matching estimate connects to eigenvalues}
\begin{center}
\begin{tikzpicture}[>=Latex,box/.style={draw,rounded corners=1pt,align=center,minimum height=1.0cm,text width=2.65cm,font=\small},node distance=.42cm]
\node[box] (a) {Expand long\\walk expressions};
\node[box,right=of a] (b) {Average products\\of matching entries};
\node[box,right=of b] (c) {Control eigenvalues\\using walk counts};
\draw[->,thick] (a)--(b);\draw[->,thick] (b)--(c);
\end{tikzpicture}
\end{center}
The product estimate supplies the middle step.

The complete graph theorem also needs separate walk-counting and local-cycle estimates.
The report cites those inputs; the product estimate alone is not a new graph spectral theorem.
\end{frame}

\begin{frame}{A half-edge is one end of a future edge}
Attach one small connector, or \emph{half-edge}, for each required neighbor.
Pair one left connector with one right connector to create a full edge.
\begin{center}\Afig[height=3.3cm,width=.96\textwidth,keepaspectratio]{teaching-halfedges}\end{center}
Two left vertices with three connectors each and three right vertices with
two each both supply six connectors. A perfect matching joins the connectors.
This is the idea behind a \emph{biregular} model: one fixed degree on each side.
\end{frame}
'''

closing = r'''\begin{frame}{What is new, and what came before?}
\begin{block}{The main new result of this report}
A proved recovery guarantee for the stated sparse random models,
with unknown count tables and a proved bound on average computation.
\end{block}
Fellows--Koblitz studied hidden fibers in four-vertex-template covers in 1993.
Bernstein--Cottaar--Lange used Gaussian elimination to expose such fibers in 2023.

The extension is in the proved range and cost guarantee. The algebraic idea
and the classical counting tools have these predecessors.
\source{The report credits prior work and does not certify historical firstness.}
\end{frame}
'''

body = [preamble,frames[0],route,'\n\\section{Graphs and matrices}\n']
body.extend(frames[2:5]);body.append(matching);body.extend(frames[5:11])
body.append('\n\\section{The Laplacian and partitioning}\n');body.extend(frames[11:18])
body.append('\n\\section{Pairings, lifts, and Proposition 28}\n');body.append(pairings)
centering_frames = re.findall(r'\\begin\{frame\}.*?\\end\{frame\}',centering,re.S)
body.extend([frames[19],centering_frames[0],frames[21]])
# Make the two-cell picture's meaning explicit for beginners.
body[-1] = body[-1].replace('The pattern of requested cells determines how much cancellation occurs.',
    'The dots mark the two entries being averaged, not a complete realized matching.\nThe position of those entries determines the cancellation.')
body.extend(centering_frames[1:])
body.append((ROOT/'present/slides/recovery-simple.tex').read_text())
body.append(closing)
body.extend([frames[44],frames[45].replace('original matching-product proofs followed\nby the condensed recovery extension and its technical proofs.',
    'Proposition 28, followed by the main recovery theorems and their complete proofs.')])
body.append(r'''\appendix
\section{Backup: precise statements and calculations}
\begin{frame}{Backup: technical details}
The main talk used a graph example and the equal-degree case.
These optional slides state the broader hypothesis and the algebra behind the algorithm.
\end{frame}
''')
for i in [20,23,25,29,30,36,37,40,41]:
    frame=frames[i]
    if i==20:
        frame=frame.replace('A perfect matching is a permutation matrix',
                            'Pairing two equal sides gives a permutation matrix')
    if i==23:
        frame=frame.replace('Let $\\mu_j=',
            'After $r$ pairs are fixed, $U$ has size $N-r$. Set\n'
            '$Z_{ij}=NU_{ij}-1$; each remaining row sums to $r$.\n\nLet $\\mu_j=')
    if i==25:
        frame=r'''\begin{frame}{Backup: the centered-product bound}
\small
Each color labels one independent uniformly random matching.
Let $P$ be a product of entries $M_{ij}$ and centered entries $M_{ij}-1/N$,
allowing repeated factors, involving $a$ distinct requested cells.

A \emph{centered singleton} is a cell used exactly once, as $M_{ij}-1/N$.
Let $h$ count such cells that share neither their row nor their column
with another requested cell of the same matching; let $b$ count the others.

For $2\le a\le\sqrt N$,
\[
 |\E P|\le\sqrt e\,2^bN^{-a}
 \left(\frac{\sqrt{a-1}}{\sqrt N-\sqrt{a-1}}\right)^h.
\]
This is the report's scalar mixed-product estimate. Its full proof
appears before the main recovery result.
\end{frame}'''
    body.append(frame)
body.append('\n\\end{document}\n')
source='\n\n'.join(body)
(ROOT/'spectral-gap-slides.tex').write_text(source)
print('Wrote',len(re.findall(r'\\begin\{frame\}',source)),'frames.')
