from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parents[2]
old_path=ROOT/'spectral-gap/submission-round-01/packages/v3/report.tex'
old=old_path.read_text()
base=ROOT/'spectral-gap/regular-community-recovery'
parts=[]; bindings={}
for name in ['02-unknown-frame','03-frame-moments','05-full-kernel','06-vector-algorithm']:
    path=base/'sections'/f'{name}.tex'; s=path.read_text()
    bindings[str(path.relative_to(ROOT))]=hashlib.sha256(path.read_bytes()).hexdigest()
    if name=='02-unknown-frame':
        s=s.replace('excluded. The exact cycle obstruction appears in\nSection~\\ref{sec:lift-boundary}.','excluded.')
    s=re.sub(r'\\(label|ref|eqref|pageref|autoref)\{([^}]+)\}',lambda m:'\\'+m[1]+'{rec:'+m[2]+'}',s)
    s=re.sub(r'(\\cite(?:\[[^]]*\])*)\{([^}]+)\}',lambda m:m[1]+'{'+','.join('rec:'+x for x in m[2].split(','))+'}',s)
    parts.append('% BEGIN COMPLETE RECOVERY PROOF: '+name+'\n'+s+'\n% END COMPLETE RECOVERY PROOF\n')
# Keep only bibliography items cited by the appended material.
refs=(base/'references.tex').read_text()
items=dict(re.findall(r'\\bibitem\{([^}]+)\}\s*(.*?)(?=\\bibitem\{|\\end\{thebibliography\})',refs,re.S))
keys=['Wiedemann','Chen','Rabin','KidKrypto','BCL','Vontobel','MoriTanaka','Meszaros']
new_bib='\n% References for the recovery extension.\n'+''.join('\\bibitem{rec:'+k+'}\n'+items[k].strip()+'\n\n' for k in keys)
macros=r'''
% Notation for the added recovery sections; original notation is preserved.
\usepackage{longtable}
\providecommand{\one}{\mathbf 1}
\providecommand{\Prob}{\mathbb P}
\providecommand{\Fp}{\mathbb F_p}
\providecommand{\F}{\mathbb F}
\providecommand{\Q}{\mathbb Q}
\providecommand{\Z}{\mathbb Z}
\providecommand{\rank}{\operatorname{rank}}
\providecommand{\nullity}{\operatorname{nullity}}
\providecommand{\supp}{\operatorname{supp}}
\providecommand{\Var}{\operatorname{Var}}
\providecommand{\spec}{\operatorname{spec}}
\providecommand{\TV}{\operatorname{TV}}
\providecommand{\KL}{D_{\mathrm{KL}}}
\providecommand{\im}{\operatorname{im}}
\providecommand{\nnz}{\operatorname{nnz}}
\providecommand{\eps}{\varepsilon}
'''
editorial=r'''
\paragraph{Expanded edition: exact hidden-group recovery.}
The opening abstract and submission record above describe the original
report, whose mathematical text is preserved in Sections~1--10 and
Appendices~A--B. The added Section~\ref{sec:recovery-overview} states a
separate recovery theorem, explains its meaning and algorithm, and points
to its complete proofs in Appendices~\ref{rec:sec:unknown-frame}--\ref{rec:sec:vector-algorithm}.
This extension studies exact hidden groups in specified random graphs;
it does not derive a new graph-norm theorem from the row-sum recurrence.
The results are research claims with internal proof review, not an
external peer-review or historical-priority certificate.
'''
overview=r'''
\clearpage
\section{Exact hidden-group recovery without spectral separation}
\label{sec:recovery-overview}
The preceding sections control products arising from random matchings.
We now turn to a different question about networks assembled from sparse
random factors: can one recover groups whose labels have been erased?
The new theorem combines an identifiability statement with a complete
algorithm and an expected-work bound. Its proof uses finite-field moment
counting and certified linear algebra, rather than the row-sum recurrence
alone. This section gives the statements and interpretation; the full
technical arguments are included in Appendices~\ref{rec:sec:unknown-frame}--\ref{rec:sec:vector-algorithm}.

\subsection{The model and the main theorem}
An \emph{equitable partition} is a division of the vertices into nonempty
groups such that every member of group $i$ has exactly $d_{ij}$ neighbors
in group $j$. The table $Q=(d_{ij})$ is its \emph{degree frame}. These are
integer equalities, not average densities. If $J$ is the matrix whose
$i$th column indicates membership in group $i$, then
\[
                         AJ=JQ.
\]
Indeed, $(AJ)_{vi}$ counts the neighbors of $v$ in group $i$, while
$(JQ)_{vi}=d_{ji}$ when $v$ belongs to group $j$. This proves both the
identity for an equitable partition and its converse for a one-hot $J$.

Fix constants $K\ge1$ and $D\ge3$. An unknown frame has $k\le K$ groups,
maximum total degree at most $D$, and connected type support. Positive
group sizes grow in fixed proportions and satisfy
$N_id_{ij}=N_jd_{ji}$ and $N_id_{ii}$ even. Independently sample a uniform
simple regular graph within each group and a uniform simple biregular
graph between each pair, with these prescribed degrees. Absent factors
are omitted. Limits are through sizes for which the simple factors exist.
The algorithm receives the graph and $K,D$, but not $k,Q$, group sizes,
or the partition.

The following sufficient condition is a finite feasibility test on $Q$:
\begin{equation}\label{eq:overview-certificate}
 q_{ij}=q_{ji},\qquad 0\le q_{ij}<\tfrac12,\qquad
                     \sum_jd_{ij}q_{ij}=1.
\end{equation}
In words, assign symmetric weights to connection types so that the
weights of all links incident to a vertex add to one. Every weight is
strictly below one half. Zero weights are allowed. The weights certify
that the theorem applies; the algorithm is not given them.

\begin{theorem}[Main recovery theorem]\label{thm:report-recovery}
In this model, assume \eqref{eq:overview-certificate}, and put
$d_{\min}=\min_i\sum_jd_{ij}$. With failure probability
$O_{K,D}(n^{-(d_{\min}-2)})$, every equitable partition into at most $K$
nonempty groups is obtained by merging whole planted groups.
Consequently the plant is the unique finest such partition, up to names.

An always-correct randomized algorithm lists all equitable partitions
with at most $K$ groups in unconditional expected
$\widetilde O_{K,D}(n^2)$ bit operations, expected
$\widetilde O_{K,D}(n)$ working bits, and expected $O_{K,D}(n)$ output
bits. Choosing the largest group count recovers the unknown plant,
frame, and sizes on the stated event.
\end{theorem}
\begin{proof}
The structural assertion, including the stated failure exponent, is
proved in Theorem~\ref{rec:thm:unknown-frame}. The raw moment bound in
Corollary~\ref{rec:thm:frame-bounded-moment} applies to every member of the
fixed finite quotient family. The complete right-kernel construction
of Theorem~\ref{rec:vec:thm:kernel}, averaged in
Theorem~\ref{rec:vec:thm:moment}, therefore gives the listing bounds.
Every true partition is in the complete list and every accepted candidate
passes its original integer equations. On the structural event all
partitions coarsen the plant, so a maximum-class member is the plant.
The full proofs of these inputs are included below, without a dependency
on a separate unpublished manuscript.
\end{proof}

\paragraph{What the conclusion means.}
The algorithm does not merely find a plausible grouping. It lists all
bounded-group answers that satisfy the exact rules. Usually the finest
answer is the one originally hidden. The bound $K$ is essential:
putting every vertex in its own group always gives an equitable
partition, so unrestricted ``finest partition'' would be a different
and trivial target. ``Expected'' includes rare graphs with many
candidates. It does not mean nearly quadratic worst-case work.

\begin{corollary}[All fixed regular templates]\label{cor:report-lifts}
Let $H$ be any fixed connected simple $d$-regular graph, $d\ge3$.
Replace each vertex of $H$ by $N$ vertices and each edge by an independent
uniform perfect matching between the corresponding groups. Given the
resulting graph and fixed order/degree bounds, the theorem recovers the
hidden groups and $H$ with probability tending to one as $N\to\infty$
through all positive integers, in expected nearly quadratic bit work.
\end{corollary}
\begin{proof}
Take $Q=A(H)$ and $q_{ij}=1/d$ on every present edge. Then
\eqref{eq:overview-certificate} holds. The factors are exactly the
independent matchings in the theorem and the lifted graph is automatically
simple. Apply Theorem~\ref{thm:report-recovery}; equivalently, see the full
specialization in Corollary~\ref{rec:vec:cor:lift}.
\end{proof}

\subsection{Two concrete examples}
\paragraph{Two groups in a cubic graph.}
Suppose every vertex has two neighbors in its own group and one in the
other. The degree frame and an omission certificate are
\[
 Q=\begin{pmatrix}2&1\\1&2\end{pmatrix},\qquad
 q_{11}=q_{12}=q_{22}=\tfrac13.
\]
Both row sums in \eqref{eq:overview-certificate} are one. Let $s_v=1$ on
one group and $s_v=-1$ on the other. A vertex in the first group has
neighbor sum $2-1=1$; one in the other has sum $1-2=-1$. Hence
$As=s$. This derives the planted eigenvector directly from the exact
neighbor counts. Recovery in Theorem~\ref{thm:report-recovery} does not
require the eigenvalue $1$ to be separated from the rest of the spectrum.
A triangular prism is a small deterministic illustration of this table:
two triangles supply the internal degree two, and the three joining
edges supply the cross degree one. The theorem itself concerns the
specified growing random model, not a finite-size claim about all prisms.

\paragraph{A regular template and an unequal-degree template.}
For a four-vertex complete template $K_4$, every template vertex has
three neighbors; assigning weight $1/3$ to each template edge gives the
certificate. The same argument works for every fixed simple regular
template of degree at least three.
The criterion also includes some unequal-degree templates. In $K_5$
with one edge removed, assign weight $1/3$ to every edge incident to a
degree-three vertex and $1/6$ to every edge between degree-four vertices.
A degree-three row sums to $3/3=1$; a degree-four row sums to
$2/3+2/6=1$. This verifies the hypothesis explicitly.
We use the full certificate, rather than assuming a minimum-degree
condition alone establishes it.

\subsection{How the algorithm works and why its cost is bounded}
For fixed $K,D$, there are only finitely many integer count tables with
at most $K$ rows and row totals at most $D$. The algorithm tries those
tables. For each candidate $R$, it solves
\[
                              AY=YR
\]
over a fixed small finite field, such as arithmetic modulo three.
The field solutions form a vector space, computed through a complete
kernel basis with a deterministically checkable completeness certificate.
The algorithm enumerates this space and retains only one-hot matrices
with nonempty columns that satisfy the original integer neighbor counts.
Thus modular coincidences can create candidates, but cannot create a
false accepted answer.

Why does this avoid an uncharged exponential search? If $h_R(A)$ is the
finite-field kernel dimension, the candidate space has $p^{h_R(A)}$
elements. Appendix~\ref{rec:ch:sec:channel-proof} proves the actual-law
raw expectation
\[
                              \sup_n\E p^{h_R(A)}<\infty
\]
for each fixed field and target. Appendix~\ref{rec:sec:full-kernel}
certifies the \emph{entire} kernel on every input, including inputs with
large nullity. Appendix~\ref{rec:sec:vector-algorithm} charges the work
before averaging. The proof therefore counts the cost of unusual inputs;
it does not discard them or send them to an uncharged fallback.
The logarithmic factors suppressed by $\widetilde O$ and the constants
depend on fixed parameters. No small practical constant or implementation
benchmark is asserted.

\subsection{Significance, predecessors, and limits}
The contribution is the combination of unknown count tables, a bounded
number of groups, all admissible sizes, sparse independent factors,
complete certification, and an unconditional expected-work guarantee.
It separates three questions: whether the hidden groups are usually
identifiable, whether every valid answer can be listed correctly, and
whether the complete computation has a proved average cost.

Algebraic fiber recovery has direct predecessors. Fellows--Koblitz's
Kid Krypto work discussed the four hidden fibers of $K_4$ covers
\cite{rec:KidKrypto}; Bernstein--Cottaar--Lange later used echelon
reduction and grouping of affine expressions to expose such fibers
\cite{rec:BCL}. We do not claim to originate Gaussian recovery.
Graph-cover counting and entropy \cite{rec:Vontobel}, positive interior
prefactors \cite{rec:MoriTanaka}, and finite-group mixing
\cite{rec:Meszaros} likewise have established predecessors.
The exact scope and composition proved here should be assessed against
that literature; this report does not certify historical firstness.

All parameters are fixed as the graph grows, the factor choices have
the stated independent uniform laws, and neighbor counts are exact.
Missing or added edges need not preserve the equations. No noise-stability,
growing-parameter, arbitrary-network clustering, numerical-eigengap,
or practical-speed theorem follows. The always-correct guarantee concerns
listing; identifying the particular plant additionally uses the high-
probability structural theorem. Finite checks and internal mathematical
reviews supplement the written proofs and do not constitute formal
verification or external peer review.

\paragraph{Proof map.}
Appendix~\ref{rec:sec:unknown-frame} proves rigidity from the certificate.
Appendix~\ref{rec:ch:sec:channel-proof} supplies the raw finite-field moment,
including zero-weight cases. Appendix~\ref{rec:sec:full-kernel} proves the
certified symmetric-kernel primitive. Appendix~\ref{rec:sec:vector-algorithm}
reduces general quotient equations to certified right kernels and completes
the expected-cost and recovery argument. These proofs are included so
that the short statement above can be read independently of the technical
details without removing those details from the formal report.

'''

# Revised architecture requested by the user: prior proof first, then the
# main recovery result AND its full proofs, quantitative refinements later.
blocks=dict(re.findall(r'% Begin preserved mathematical section: ([^\n]+)\n(.*?)% End preserved mathematical section',old,re.S))
assert len(blocks)==12, blocks.keys()
intro=(ROOT/'present/report/revised-introduction.tex').read_text()
abstract=(ROOT/'present/report/revised-abstract.tex').read_text()
old_intro=blocks['sections/introduction']
qsummary=old_intro[old_intro.index('\\subsection{Main results at a glance}'):]
qsummary=qsummary.replace('\\subsection{Main results at a glance}', '\\section{Supplementary moment notation and result summary}\\label{sec:moment-summary}',1)
qsummary=qsummary.replace('The main conclusions are as follows.', 'The supplementary moment conclusions are as follows.',1)
normalization=old_intro[old_intro.index('For the diagonal product'):old_intro.index('\\subsection{Main results at a glance}')]
qheader='\\section{Supplementary moment notation and result summary}\\label{sec:moment-summary}'
qsummary=qsummary.replace(qheader,qheader+'\n\n'+normalization,1)
# Retain the original historic submission record, explicitly as history.
record=old.split('\\section*{Submission record and reading route}',1)[1].split('\\clearpage',1)[0]
record=record.replace('\\addcontentsline{toc}{section}{Submission record and reading route}','',1)
history=r"""\clearpage
\section{Historical submission record and checking details}\label{sec:historical-record}
This section preserves the original submission record for the earlier
moment report. References to its original scope and presentation describe
that historical version, not the main recovery results now proved in
Sections~\ref{sec:recovery-overview}--\ref{rec:sec:vector-algorithm}.
The mathematical content and current scope are stated in the abstract,
introduction, and theorem statements of the present report.
"""+record
# All previously appended recovery arguments are now MAIN-TEXT sections.
overview=overview.replace('Appendices~\\ref{rec:sec:unknown-frame}--\\ref{rec:sec:vector-algorithm}', 'Sections~\\ref{rec:sec:unknown-frame}--\\ref{rec:sec:vector-algorithm}')
overview=overview.replace('Appendix~\\ref{rec:', 'Section~\\ref{rec:')
# Keep the old introduction's normalization and every theorem/proof.
appendices=[qsummary]
for name in ['threshold','critical','extensions','asymptotics','rates','conditioning','discussion','rate-proof','global-sharp-proof']:
    block=blocks['sections/'+name]
    if name=='discussion':
        block=block.replace('\\section{Contribution, limitations and further questions}', '\\section{Prior work and limits of the moment refinements}\\label{sec:moment-discussion}',1)
    appendices.append(block)
# Add the closest recovery references explicitly credited in the new intro.
for key in ['BDGHT','Barucca','KP']:
    new_bib+='\\bibitem{rec:'+key+'}\n'+items[key].strip()+'\n\n'
preamble=old.split('\\begin{document}',1)[0]+macros
preamble=preamble.replace('Gaps in spectral-gap literature:\\\\ a row-sum proof and its spectral role', 'Centered permutation estimates\\\\ and exact recovery in sparse graphs')
preamble=preamble.replace('pdftitle={Gaps in spectral-gap literature}', 'pdftitle={Centered permutation estimates and exact recovery in sparse graphs}')
preamble=preamble.replace('pdfsubject={Problem 21: a row-sum proof and its spectral role}', 'pdfsubject={Proposition 28 and certified unknown-frame recovery}')
old_bibliography='\\begin{thebibliography}{99}'+old.split('\\begin{thebibliography}{99}',1)[1].split('\\end{thebibliography}',1)[0]
s=preamble+'\n\\begin{document}\n\\maketitle\n\\begin{abstract}\n'+abstract+'\\end{abstract}\n\\clearpage\n\\begingroup\\small\n\\tableofcontents\n\\endgroup\n\\clearpage\n'+intro
s+='\n'+blocks['sections/mixed']+'\n'+blocks['sections/spectral']+'\n'+overview
s+='\n\\clearpage\n'+'\n\\clearpage\n'.join(parts)
s+='\n\\clearpage\n\\appendix\n'+'\n\\clearpage\n'.join(appendices)+'\n'+history
s+='\n\\clearpage\n'+old_bibliography+new_bib+'\\end{thebibliography}\n\\end{document}\n'
(ROOT/'spectral-gap-report.tex').write_text(s)
meta={'original_source':str(old_path.relative_to(ROOT)),'original_sha256':hashlib.sha256(old.encode()).hexdigest(),'recovery_modules':bindings,'edits_to_modules':['Prefix labels, references and citations with rec:','Remove one expository cycle-obstruction reference from02; no proof changed'],'new_source_sha256':hashlib.sha256(s.encode()).hexdigest(),'structure':'Main1introduction/priorwork;2Prop28proof;3spectralrole;4recoverytheorem;5--8complete recoveryproofs;quantitative appendixA--J;historicalrecordK;unifiedreferences','revision':'User requested recovery prominence in abstract,introduction,and main proofs; priorwork and Proposition28 still come first.'}
(ROOT/'present/report/source-provenance.json').write_text(json.dumps(meta,indent=2)+'\n')
print('Wrote revised report',len(s),'characters.')
