\documentclass{llncs}
\usepackage{a4}
\usepackage{upgreek}

%if False
\begin{code}
{-# OPTIONS --copatterns #-}
module Totality where

_o_ : {A : Set}{B : A -> Set}{C : (a : A) -> B a -> Set}
  (f : {a : A}(b : B a) -> C a b)(g : (a : A) -> B a) ->
  (a : A) -> C a (g a)
f o g = \ x -> f (g x)
infixr 2 _o_
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

\title{Totality versus Turing-Completeness?}
\author{Conor McBride}
\institute
  {University of Strathclyde\\
   \email{conor@@strictlypositive.org}
  }

\begin{document}
\maketitle

\section{Introduction}

Advocates of Total Functional Programming~\cite{Turner04}, amongst
whom I number, can prove prone to a false confession, namely that the
price to ensure functions are worthy of the name is the loss of
Turing-completeness. In a total functional programming language, to
construct a value $f : S\to T$ is to promise a canonical $T$
eventually, given a canonical $S$. The alleged benefit of general
recursion is just to inhibit the making of such a promise. To make a
weaker promise, one need merely construct a total function of type
$S\to G\:T$ where $G$ is a suitably chosen monad.

The literature and lore of our discipline are littered with candidates
for $G$, and this article will contribute another---the \emph{free}
monad with one operation $f : S\to T$. To work in such a monad is to
\emph{write} a general recursive function without prejudice as to how
it might be \emph{executed}. We are then free, in the technical sense,
to choose any semantics for general recursion we like, including one
which captures permission to execute unless interrupted by
control-C. Indeed, the latter semantics is delivered by Venanzio Capretta's partiality
monad~\cite{DBLP:journals/lmcs/Capretta05}, also known as the
\emph{completely iterative} monad on the operation
$\mathit{yield}:1\to 1$, which might never deliver a value but periodically
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

%format forall = "\mathkw{\forall}"
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


\textbf{For crying out loud, construct these things as monad morphisms.}
%format foldGen = "\F{foldGen}"
\begin{code}
foldGen :  forall {S}{T}{X Y : Set} ->
           (X -> Y) -> ((s : S) -> (T s -> Y) -> Y) ->
           General S T X -> Y
foldGen r c (return x)     = r x
foldGen r c (command s k)  = c s \ t -> foldGen r c (k t)
\end{code}
\textbf{Assume ext and show that always generates monad morphisms.}


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
expand f = foldGen return (_>>=_ o f)
\end{code}
%format gf = "\F{f}"
You will have noticed that |call : PiG S T|, and that |expand call| just
replaces one |command| with another, acting as the identity. As a recursive
strategy, taking |f = \ s -> call s| amounts to the often valid but seldom helpful
`definition':
\[
  |gf s = gf s|
\]


By way of example, let us consider the evolution of state machines. We shall
need Boolean values:
%format Bool = "\D{Bool}"
%format tt = "\C{t\!t}"
%format ff = "\C{f\!f}"
%format if = "\F{if}"
%format then = "\F{then}"
%format else = "\F{else}"
%format if_then_else_ = if _ then _ else _
\begin{code}
data Bool : Set where tt ff : Bool

if_then_else_ : {X : Set} -> Bool -> X -> X -> X
if tt then t else f = t
if ff then t else f = f
\end{code}
Now let us construct the method for computing the halting state of a machine,
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

An amusing possibility in a system such as Agda, supporting the
partial evaluation of incomplete expressions, is to invoke |petrol|
with |?| as the quantity of fuel. We are free to refine the |?| with
|suc ?| and resume evaluation repeatedly for as long as we are
willing to wait in expectation of a |yes|. Whilst this may be a clunky
way to signal continuing consent for execution, compared to the simple
maintenance of the electricity supply, it certainly simulates the
conventional experience of executing a general recursive
program.

What, then, is the substance of the often repeated claim that a total
language capable of this construction is not Turing-complete?  Just
this: there is more to delivering the run time execution semantics of
programs than the pure evaluation of expressions. The \emph{language}
might thus be described as Turing-incomplete, even though the
\emph{system} by which you use it allows you to execute arbitrary
recursive computations for as long as you are willing to tolerate.
Such a pedantic quibble deserves to be taken seriously inasmuch as it
speaks against casually classifying a \emph{language} as
Turing-complete or otherwise, without clarifying the variety of its
semanticses and the relationships between them.


\section{Capretta's Coinductive Semantics}

Coinduction in dependent type theory remains a vexed issue: we are gradually
making progress towards a presentation of productive programming for infinite
data structures, but we can certainly not claim that we have a presentation
which combines honesty, convenience and compositionality. Here, I shall need
only the first of those virtues, so I shall make do with the current Agda
account, based on the notion of \emph{copatterns}~\cite{DBLP:conf/popl/AbelPTS13}.
The copattern literature tends to give examples of copattern programming
involving only product structures, notably streams, but Capretta requires us
to risk a sum.

%format + = "\D{+}"
%format _+_ = _ + _
%format inl = "\C{inl}"
%format inr = "\C{inr}"
\begin{code}
data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

[_,_] : {S T X : Set} -> (S -> X) -> (T -> X) -> S + T -> X
[ f , g ] (inl s) = f s
[ f , g ] (inr t) = g t
\end{code}

%format Delay = "\D{Delay}"
%format force = "\F{force}"
%format coinductive = "\mathkw{coinductive}"
We may now define the indefinite |Delay| operator as a coinductive record type
whose values are constructed on demand, when the |force| field is projected.
\begin{code}
record Delay (X : Set) : Set where
  coinductive
  field
    force : X + Delay X
open Delay
\end{code}

Thus equipped, we can build a |Delay X| value by stepping a computation
which can choose either to deliver an |X| or to continue.

Sadly, the following code fails Agda's rather syntactic productivity check.
%format unfold = "\F{unfold}"
%format help = "\F{help}"
%format o = "\F{\cdot}"
\begin{spec}
unfold : forall {X Y} -> (Y -> X + Y) -> Y -> Delay X
force (unfold f y) = [ inl , inr o unfold f ] (f y)
\end{spec}
However, brute force inlining of the case analysis saves the day.
\begin{code}
unfold : forall {X Y} -> (Y -> X + Y) -> Y -> Delay X
force (unfold {X}{Y} f y) = help (f y) where
  help : X + Y -> X + Delay X
  help (inl x)  = inl x
  help (inr y)  = inr (unfold f y)
\end{code}

%format _D>=_ = _>>=_
%format lego = "\F{lego}"
%format rigo = "\F{rigo}"
Capretta explored the use of |Delay| as a monad to model general recursion,
giving a presentation of a language with an operator seeking the minimum number
satisfying a test. Given |unfold|, we may equip |Delay| with a `bind' operator.
At any stage, we are executing either the first computation\footnote{For legal
reasons, I note that the function |lego|, below, has no connection with the
proof assistant of that name.} |dx : Delay X|
or its continuation, instantiated with a given |x|.%format D>= = >>=
\begin{code}
Dret : forall {X} -> X -> Delay X
force (Dret x) = inl x

later : forall {X} -> Delay X -> Delay X
force (later dx) = inr dx

_D>=_ : forall {X Y} -> Delay X -> (X -> Delay Y) -> Delay Y
_D>=_ {X}{Y} dx k = unfold [ lego , rigo ] (inl dx) where
  rigo : Delay Y -> Y + (Delay X + Delay Y)
  rigo dy with force dy
  ... | inl y    = inl y            -- finished
  ... | inr dy'  = inr (inr dy')    -- running |k x|
  lego : Delay X -> Y + (Delay X + Delay Y)
  lego dx with force dx
  ... | inl x    = rigo (k x)       -- invoking |k| with |x|
  ... | inr dx'  = inr (inl dx')    -- running |dx|
\end{code}


By way of connecting the Capretta semantics with the petrol-driven variety,
we may equip every |Delay| process with a monotonic |engine|.
%format engine = "\F{engine}"
\begin{code}
engine : forall {X} -> Delay X -> Nat -> Maybe X
engine dx n        with force dx
engine dx n        | inl x    = yes x
engine dx zero     | inr _    = no
engine dx (suc n)  | inr dx'  = engine dx' n
\end{code}

%format tryMorePetrol = "\F{tryMorePetrol}"
%format try = "\F{try}"
%format minimize = "\F{minimize}"
Moreover, given a petrol-driven process, we can just keep trying more and more
fuel. This is one easy way to write the minimization operator.
\begin{code}
tryMorePetrol : forall {X} -> (Nat -> Maybe X) -> Delay X
tryMorePetrol {X} f = unfold try zero where
  try : Nat -> X + Nat
  try n  with  f n
  ...    |     yes x  = inl x
  ...    |     no     = inr (suc n)

minimize : (Nat -> Bool) -> Delay Nat
minimize test = tryMorePetrol \ n -> if test n then yes n else no
\end{code}

Our command-response characterization of general recursion is readily
mapped onto |Delay|. The coalgebra of the |unfold| just expands the topmost
node of the call graph.
%format delay = "\F{delay}"
%format go = "\F{go}"
\begin{code}
delay : forall {S T} -> PiG S T -> (s : S) -> Delay (T s)
delay {S}{T} f s = unfold go (f s) where
  go : forall {X} -> General S T X -> X + (General S T X)
  go (return t)     = inl t
  go (command s g)  = inr (f s >>= g)
\end{code}

\section{Completely Iterative Monads}

The \emph{completely iterative} monad generated by a command-response system
is given by the possibly infinite command-response trees with values at whatever
leaves may be reachable. When we inspect the top of such a tree, we will find
either a leaf or the dependent pair of a command and its resumption.

%format Sg = "\D{\Upsigma}"
%format , = "\C{,}\:"
%format fst = "\F{fst}"
%format snd = "\F{snd}"
%format constructor = "\mathkw{constructor}"
%format comIt = "\F{comIt}"
%format ComIt = "\D{ComIt}"
%format cocall = "\F{call}"
%format top = "\F{top}"
\begin{code}
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst  : S
    snd  : T fst
open Sg

record ComIt (S : Set)(T : S -> Set)(X : Set) : Set where
  coinductive
  field
    top : X + Sg S \ s -> T s -> ComIt S T X
open ComIt
\end{code}

As with |Delay|, let us minimize our reliance on Agda's built in treatment of
coinduction and generate completely iterative computations only by
unfolding coalgebras. 

\begin{code}

comIt :  forall {S T X Y} ->
         (Y -> X + Sg S \ s -> T s -> Y) -> Y -> ComIt S T X
top (comIt {S}{T}{X}{Y} f y) = help (f y) where
  help : (X + Sg S \ s -> T s -> Y) -> X + Sg S \ s -> T s -> ComIt S T X
  help (inl x)        = inl x
  help (inr (s , k))  = inr (s , \ t -> comIt f (k t))

cocall : forall {S T} -> (s : S) -> ComIt S T (T s)
cocall {S}{T} s = comIt go no where
  go : Maybe (T s) -> T s + Sg S \ s' -> T s' -> Maybe (T s)
  go no       = inr (s , yes)
  go (yes t)  = inl t
\end{code}

The `bind' for the completely iterative monad is definable via |comIt| using
the same kind of coalgebra as we used for |Delay|.
%format _C>=_ = _>>=_
\begin{code}
_C>=_ :  forall {S T X Y} ->
         ComIt S T X -> (X -> ComIt S T Y) -> ComIt S T Y
_C>=_ {S}{T}{X}{Y} cx k = comIt [ lego , rigo ] (inl cx) where
  rigo : ComIt S T Y -> Y + Sg S \ s -> T s -> ComIt S T X + ComIt S T Y
  rigo cy with top cy
  ... | inl y        = inl y
  ... | inr (s , g)  = inr (s , \ t -> inr (g t))
  lego : ComIt S T X -> Y + Sg S \ s -> T s -> ComIt S T X + ComIt S T Y
  lego cx with top cx
  ... | inl x        = rigo (k x)
  ... | inr (s , g)  = inr (s , \ t -> inl (g t))
\end{code}

%format One = "\D{One}"
%format <> = "\C{\langle\rangle}"
%format DELAY = "\F{DELAY}"
%format yield = "\F{yield}"
It should thus be no surprise that the |Delay| monad can be seen as
the trivial instance of |ComIt|. The generic effect is the operation whose input
and output carry no information: it amounts to |yield|ing control to the environment,
offering no data, except a continuation to be invoked with no new information. The
environment can choose whether or not the continuation gets invoked.

%format DELAY = "\F{Delay}"
\begin{code}
record One : Set where constructor <>

DELAY  :  Set -> Set
DELAY  =  ComIt One \ _ -> One

yield  :  One -> DELAY One
yield  _  = cocall <>
\end{code}





\section{An Introduction or Reimmersion in Induction-Recursion}

\textbf{And remember, IR codes form a free (relative) monad.}

%format IR = "\D{IR}"
%format iota = "\C{\upiota}"
%format sigma = "\C{\upsigma}"
%format delta = "\C{\updelta}"
%format <! = "\F{\llbracket}"
%format !> = "\F{\rrbracket}"
%format !>Set = !> "_{\D{Set}}"
%format <!_!>Set = <! _ !>Set
%format !>out = !> "_{\F{out}}"
%format <!_!>out = <! _ !>out
%format -:> = "\F{\dot{\to}}"
%format _-:>_ = _ -:> _
%format Mu = "\D{\upmu}"
%format decode = "\F{decode}"
%format oo = "\V{o}"
%format << = "\C{\langle}"
%format >> = "\C{\rangle}"
%format <<_>> = << _ >>
%format IndRec = "\F{IndRec}"
%format IndRecType = "\F{IndRecType}"
%format IndRecDescription = "\F{IndRecDescription}"
%format IndRecInterpretation = "\F{IndRecInterpretation}"
%format IndRecDescription.IndRecInterpretation = IndRecDescription "." IndRecInterpretation
%format Dummy = "\F{Dummy}"
%format Set1 = Set "_{\D{1}}"

\begin{code}
_-:>_ : {S : Set}(X Y : S -> Set) -> Set
X -:> Y = forall {s} -> X s -> Y s

module IndRec {S : Set}(I : S -> Set) where
  data IR (O : Set) : Set1 where
    iota   : (oo : O)                                                     -> IR O
    sigma  : (A : Set)(T : A -> IR O)                                     -> IR O
    delta  : (B : Set)(s : B -> S)(T : (i : (b : B) -> I (s b)) -> IR O)  -> IR O

  <!_!>Set :  forall {O}(T : IR O)(X : S -> Set)(i : X -:> I) -> Set
  <!_!>out :  forall {O}(T : IR O)(X : S -> Set)(i : X -:> I) -> <! T !>Set X i -> O

  <! iota oo      !>Set  X i = One
  <! sigma A T    !>Set  X i = Sg A \ a -> <! T a !>Set X i
  <! delta B s T  !>Set  X i = Sg ((b : B) -> X (s b)) \ r -> <! T (i o r) !>Set X i

  <! iota oo      !>out  X i <>       = oo
  <! sigma A T    !>out  X i (a , t)  = <! T a !>out X i t
  <! delta B s T  !>out  X i (r , t)  = <! T (i o r) !>out X i t
\end{code}

\begin{code}
  module IndRecType where
    data Mu (F : (s : S) -> IR (I s))(s : S) : Set
\end{code}
%if False
\begin{code}
    {-# NO_TERMINATION_CHECK #-}  -- inlining removes the need for this
\end{code}
%endif
\begin{code}
    decode :  forall {F} -> Mu F -:> I

    data Mu F s where
      <<_>> : <! F s !>Set (Mu F) decode -> Mu F s

    decode {F}{s} << t >> = <! F s !>out (Mu F) decode t

open IndRec
open module Dummy {S}{I} = IndRec.IndRecType {S} I
\end{code}



\section{The Bove-Capretta Construction}

\textbf{It just might also be a monad morphism.}

\begin{code}
genIR : forall {S T X} -> General S T X -> IR T X
genIR (return x)     = iota x
genIR (command s k)  = delta One (\ _ -> s) \ t -> genIR (k (t <>))

DOM : forall {S T} -> PiG S T -> (s : S) -> IR T (T s)
DOM f s = genIR (f s)

bove : forall {S T}(f : PiG S T) -> ((s : S) -> Mu (DOM f) s) -> (s : S) -> T s
bove f allInDom = decode o allInDom
\end{code}



\section{The Graph Construction and Graph Induction}


\section{Conclusion}


\bibliographystyle{plainnat}
\bibliography{Totality.bib}

\end{document}
