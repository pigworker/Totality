\documentclass{article}
\usepackage{a4}

%if False
\begin{code}
module Totality where
\end{code}
%endif

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}

\ColourStuff

\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\C}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\purple{\mathit{#1}}}
\newcommand{\T}[1]{\raisebox{0.02in}{\tiny\green{\textsc{#1}}}}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"

%format -> = "\blue{\rightarrow}"

\begin{document}
\title{Totality versus Turing-Completeness?}
\author{Conor McBride}
\maketitle

\section{Introduction}

Advocates of Total Functional Programming~\cite{Turner04}, amongst
whom I number, can prove prone to a false confession, namely that the
price to ensure functions are worthy of the name is the loss of Turing-
completeness. In a total functional programming language, to construct a
value $f : S\to T$ is to promise a canonical $T$ eventually, given a
canonical $S$. The alleged benefit of general recursion is just to inhibit
the making of such a promise. To make a weaker promise, one need merely
construct a total function of type $S\to G\:T$ where $G$ is a suitably
chosen monad.

The literature and lore of our discipline are littered with candidates
for $G$, and this article will contribute another---the \emph{free}
monad with one operation $f : S\to T$. To work in such a monad is to
\emph{write} a general recursive function without prejudice as to how
it might be \emph{executed}. We are then free, in the technical sense,
to choose any semantics for general recursion we like, including one
which captures permission to execute unless interrupted by
control-C. The latter semantics is delivered by Venanzio Capretta's partiality
monad~\cite{DBLP:journals/lmcs/Capretta05}, also known as the
\emph{completely iterative} monad on the operation
$\mathit{yield}:1\to 1$ which might never deliver a value but periodically
offers its environment the choice of whether or not to continue.

Meanwhile, Ana Bove gave, with Capretta, a method for defining the
\emph{domain predicate} of a general recursive function simultaneously
with the delivery of a value for every input satisfying that domain
predicate~\cite{DBLP:conf/tphol/BoveC01}. Their technique gives a
paradigmatic example of defining a datatype and its interpretation by
\emph{induction-recursion} in the sense of Peter Dybjer and Anton
Setzer~\cite{DBLP:conf/tlca/DybjerS99,DBLP:conf/dagstuhl/DybjerS01}.
Dybjer and Setzer further gave a coding scheme which renders first
class the characterising data for inductive-recursive definitions.  In
this article, I show how to compute from the free monadic presentation
of a general recursive function the code for its domain predicate. By
doing so, I implement the Bove-Capretta method once for all,
systematically delivering (but not, of course, discharging) the proof
obligation required to strengthen the promise from partial $f : S\to G
\: T$ to the total $f:S\to T$.

Total functional languages remain \emph{logically} incomplete in the
sense of G\"odel. There are termination proof obligations which we can
formulate but not discharge within any given total language, even
though the relevant programs are total---notably the evaluator for the
language itself. Translated across the Curry-Howard correspondence,
the argument for general recursion amounts to the assertion that
logical inconsistency is a price worth paying for logical
completeness, notwithstanding the concomitant destruction of the
logic's evidential value.  If you believe that, you believe anything.
Programmers are free to maintain that such dishonesty is essential to
their capacity to earn a living, but a new generation of programming
technology enables some of us to offer and deliver a higher standard
of guarantee. \emph{Faites vos jeux!}


\section{The General Free Monad}

Working, for example, in Agda, we may define a free monad which is
general, both in the sense of being generated by any strictly positive
functor, and in the sense of being suited to the modelling of general recursion.

%format Set = "\D{Set}"
%format General = "\D{General}"
%format return = "\C{return}"
%format command = "\C{command}"
\begin{code}
data General (S : Set)(T : S -> Set)(X : Set) : Set where
  return   : X -> General S T X
  command  : (s : S) -> (T s -> General S T X) -> General S T X
\end{code}

Values in |General S T X| are command-response trees with |X|-values at
the leaves. Each internal node is labelled by a command |s : S| and branches
over the possible meaningful responses in the dependent type |T s|. The
`bind' operation for the monad |General S T| substitutes computations for
values to build larger computations.

%format >>= = "\F{>\!\!>\!\!=}"
%format _>>=_ = _ "\!" >>= "\!" _
\begin{code}
_>>=_ :  forall {S T X Y} -> 
         General S T X -> (X -> General S T Y) -> General S T Y
return x     >>= k  = k x
command s g  >>= k  = command s \ t -> g t >>= k
\end{code}

We then acquire what Gordon Plotkin and John Power call a
\emph{generic effect} \cite{DBLP:journals/acs/PlotkinP03}---the presentation
of an individual command-response interaction:
%format call = "\F{call}"
\begin{code}
call : forall {S T} -> (s : S) -> General S T (T s)
call s = command s \ t -> return t
\end{code}

%format PiG = "\F{PiG}"
If we build a command-response tree from individual |call|s, we give a
strategy for interacting with an oracle which responds to commands |s : S|
with values in |T s|. We may thus define |PiG S T|
\begin{code}
PiG : (S : Set) -> (T : S -> Set) -> Set
PiG S T = (s : S) -> General S T (T s)
\end{code}
to be a type of recursive \emph{strategies}
for computing a |T s| from some |s : S|.
These strategies are finite: they tell us how to expand one |command| in terms
of zero or more recursive calls.
%format expand = "\F{expand}"
\begin{code}
expand : forall {S T X} -> PiG S T -> General S T X -> General S T X
expand f (return x)     = return x
expand f (command s g)  = f s >>= \ t -> expand f (g t)
\end{code}
You will have noticed that |call : PiG S T|, and that |expand call| just
replaces one |command| with another, acting as the identity. As a recursive
strategy |call = \ s -> call s| amounts to the often valid but seldom helpful
`definition':
\[
  |f s = f s|
\]

By way of example, let us consider the evolution of state machines. We shall
need Boolean values:
%format Bool = "\D{Bool}"
%format tt = "\C{t\!t}"
%format ff = "\C{f\!f}"
\begin{code}
data Bool : Set where tt ff : Bool
\end{code}
Now let us explain the method for computing the halting state of a machine,
given its initial state and its one-step transition function.
%format halting = "\F{halting}"
\begin{code}
halting : forall {S} -> (S -> Bool) -> (S -> S) -> PiG S \ _ -> S
halting stop step start  with  stop start
...                      |     tt = return start
...                      |     ff = call (step start)
\end{code}
For Turing machines, |S| should pair a machine state with a tape, |stop| should
check if the machine state is halting, and |step| should look up the current
state and tape-symbol in the machine description then return the next state
and tape. We can clearly explain how any old Turing machine computes without
stepping beyond the confines of total programming, and without making any
rash promises about what values such a computation might deliver.


\section{The Petrol-Driven Semantics}

It is one thing to describe a general-recursive computation but quite another
to perform it. A simple way to give an arbitrary total approximation to
partial computation is to provide an engine which consumes one unit of petrol
for each recursive call it performs, then specify the initial fuel supply.
The resulting program is primitive recursive, but makes no promise to deliver
a value.

%format Nat = "\D{Nat}"
%format zero = "\C{zero}"
%format suc = "\C{suc}"
%format Maybe = "\D{Maybe}"
%format yes = "\C{yes}"
%format no = "\C{no}"
%format petrol = "\F{petrol}"
%format engine = "\F{engine}"
\begin{code}
data Nat : Set where
  zero  : Nat
  suc   : Nat -> Nat

data Maybe (X : Set) : Set where
  yes  : X -> Maybe X
  no   : Maybe X

petrol : forall {S T} -> PiG S T -> Nat -> (s : S) -> Maybe (T s)
petrol {S}{T} f n s  = engine (f s) n where
  engine : forall {X} -> General S T X -> Nat -> Maybe X
  engine (return x)     _        = yes x
  engine (command s g)  zero     = no
  engine (command s g)  (suc n)  = engine (f s >>= g) n
\end{code}

If we consider |Nat| with the usual order and |Maybe X| ordered by
|no < yes x|, we can readily check that |engine c| is monotone: supplying
more fuel can only (but sadly not strictly) increase the risk of
successfully delivering output.


\bibliographystyle{plainnat}
\bibliography{Totality.bib}

\end{document}