\documentclass{llncs}
\usepackage{a4}
\usepackage{upgreek}

%if False
\begin{code}
{-# OPTIONS --copatterns #-}
module Totality where

open import Agda.Primitive
postulate
  Size : Set
  Size<_ : Size → Set
  ↑_ : Size → Size
  ∞ : Size
{-# BUILTIN SIZE Size #-}
{-# BUILTIN SIZELT Size<_ #-}
{-# BUILTIN SIZESUC ↑_ #-}
{-# BUILTIN SIZEINF ∞ #-}

_o_ : {i j k : Level}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : {a : A}(b : B a) -> C a b)(g : (a : A) -> B a) ->
  (a : A) -> C a (g a)
f o g = \ x -> f (g x)
infixr 2 _o_

data _==_ {l : Level}{X : Set l}(x : X) : X -> Set l where
  refl : x == x

id : {l : Level}{X : Set l} -> X -> X
id x = x

postulate
  .ext : forall {i j}{A : Set i}{B : A -> Set j}{f g : (a : A) -> B a} ->
        ((a : A) -> f a == g a) -> f == g

record One : Set where constructor <>


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
%format forall = "\blue{\forall}"

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
functor, and in the sense of being suited to the modelling of general
recursion.

%format Set = "\D{Set}"
%format General = "\D{General}"
%format !! = "\C{!!}"
%format ?? = "\C{??}"
%format _??_ = _ ?? _
%format o = "\F{\cdot}"
%format id = "\F{id}"
\begin{code}
data General (S : Set)(T : S -> Set)(X : Set) : Set where
  !!    : X -> General S T X
  _??_  : (s : S) -> (T s -> General S T X) -> General S T X
infixr 5 _??_
\end{code}

At each step, we either output an |X|, or we make the request
|s ?? k|, for some |s : S|, where |k| explains how to continue once a
response in |T s| has been received. That is, values in |General S T
X| are request-response trees with |X|-values at the leaves; each
internal node is labelled by a request and branches over the possible
meaningful responses.  The key idea in this paper is to represent
recursive calls as just such request-response interactions, and recursive
definitions by just such trees.

This datatype comes with a catamorphism, or `fold' operator.\footnote{Those
who would use `fold' to mean monoidal accumulation across a data structure
must be \emph{crush}ed.}
%format foldG = "\F{foldG}"
\begin{code}
foldG :  forall {l S T X}{Y : Set l} ->
         (X -> Y) -> ((s : S) -> (T s -> Y) -> Y) -> General S T X -> Y
foldG r c (!! x)    = r x
foldG r c (s ?? k)  = c s \ t -> foldG r c (k t)
\end{code}

The `bind' operation for the monad |General S T| substitutes
computations for values to build larger computations. It is, of course,
a |foldG|.

%format forall = "\mathkw{\forall}"
%format >G>= = "\F{>\!\!>\!\!=}"
%format _>G>=_ = _ >G>= _
\begin{code}
_>G>=_ :  forall {S T X Y} ->
          General S T X -> (X -> General S T Y) -> General S T Y
g >G>= k  = foldG k _??_ g
infixr 4 _>G>=_
\end{code}

We then acquire what Gordon Plotkin and John Power call a
\emph{generic effect} \cite{DBLP:journals/acs/PlotkinP03}---the presentation
of an individual request-response interaction:
%format call = "\F{call}"
\begin{code}
call : forall {S T}(s : S) -> General S T (T s)
call s = s ?? !!
\end{code}

%format Kleisli = "\D{Kleisli}"
Of course, it is one thing to claim
that |General S T| is a monad and quite another to establish that this
is the case. We shall need to introduce the definition of a monad and
confirm that it is satisfied. Moreover, we shall need to give
semantics to our request-response trees, mapping each request to
something which tries to deliver its response. We should make sure
that requests are handled consistently, which amounts to establishing
that each semantics is a monad morphism, hence we shall need to be a
little more precise about what the latter are, and how to obtain them.


\section{Monads and Monad Morphisms, More or Less}

Let us introduce the notion of a |Kleisli| structure on sets,
as Altenkirch and Reus called it, also known to Altenkirch, Chapman and
Uustalu as a `relative' monad. That is, I do not require my operation on
sets to be an \emph{endofunctor}: later, we shall make use of this
flexibility.
%format ⊔ = "\sqcup"
%format return = "\F{return}"
%format >>= = "\F{>\!\!>\!\!=}"
%format _>>=_ = _ >>= _
%format lsuc = "\C{lsuc}"
%format <-< = "\F{\diamond}"
%format _<-<_ = _ <-< _
%format idLeft = "\F{idLeft}"
%format idRight = "\F{idRight}"
%format assoc = "\F{assoc}"
%format .idLeft = "." idLeft
%format .idRight = "." idRight
%format .assoc = "." assoc
%format KleisliLaws = "\D{KleisliLaws}"
\begin{code}
record Kleisli {i j}(M : Set i -> Set j) : Set (lsuc (i ⊔ j)) where
  field
    return  : forall {X} ->    X -> M X
    _>>=_   : forall {A B} ->  M A -> (A -> M B) -> M B
  infixr 4 _>>=_
  extend : forall {A B} -> (A -> M B) -> M A -> M B
  extend f m = m >>= f
  map : forall {A B} -> (A -> B) -> M A -> M B
  map f = extend (return o f)
  _<-<_ : forall {A B C : Set i} -> (B -> M C) -> (A -> M B) -> (A -> M C)
  (f <-< g) = extend f o g
  infixr 4 _<-<_
\end{code}
Given the `return' and `bind', we may define Kleisli composition in the
usual way, replacing each value emerging from |g| with
the computation indicated by |f|. We should, of course, deliver
%format GeneralK = "\F{GeneralK}"
\begin{code}
GeneralK : forall {S T} -> Kleisli (General S T)
GeneralK = record { return = !! ; _>>=_ = _>G>=_ }
\end{code}
by way of example.

We may now specify the Monad laws by
requiring that |return| and |<-<| satisfy the laws to give us a category.
\begin{code}
record KleisliLaws {i j}{M : Set i -> Set j}(KM : Kleisli M) : Set (lsuc (i ⊔ j)) where
  open Kleisli KM
  field
    .idLeft    : forall {A B}(g : A -> M B) ->  (return <-< g)  ==  g
    .idRight   : forall {A B}(f : A -> M B) ->  (f <-< return)  ==  f
    .assoc     : forall {A B C D}(f : C -> M D)(g : B -> M C)(h : A -> M B) ->
                   ((f <-< g) <-< h) == (f <-< (g <-< h))
\end{code}
The dots before the field names make the information thus required
unavailable for computational purposes. Correspondingly, I have little
compunction about postulating an extensional equality and reasoning
with the convenient ability to transform the implementations of
functions by equational laws.
%format ext = "\F{ext}"

%format !!! = "\F{\square}"
%format _!!! = "\F{\_}" !!!
%format =! = "\F{=\!\![}"
%format !> = "\F{\rangle\!\!=}"
%format != = "\F{]\!\!=}"
%format <! = "\F{=\!\!\langle}"
%format _=!_!>_ = "\F{\_}" =! "\F{\_}" !> "\F{\_}"
%format _<!_!=_ = "\F{\_}" <! "\F{\_}" != "\F{\_}"
\newcommand{\equalityRewriting}{
\begin{code}
_=!_!>_ : forall {l}{X : Set l}(x : X){y z} -> x == y -> y == z -> x == z
x =! refl !> q = q

_<!_!=_ : forall {l}{X : Set l}(x : X){y z} -> y == x -> y == z -> x == z
x <! refl != q = q

_!!! : forall {l}{X : Set l}(x : X) -> x == x
x !!! = refl
infixr 2 _!!! _=!_!>_ _<!_!=_


<^_^> : {l : Level}{X : Set l}(x : X) -> x == x
<^_^> x = refl
_$$_ : {i j : Level}{A : Set i}{B : Set j}{f g : A -> B}{a a' : A} ->
  f == g -> a == a' -> f a == g a'
refl $$ refl = refl
infixl 2 _$$_
\end{code}}

Let us warm up to the proofs of the laws by establishing some basic
properties of |foldG|. Firstly, let us show that anything satisfying
the defining equations of a |foldG| can be given as a |foldG|.
\begin{code}
.foldGUnique : forall {l S T X}{Y : Set l}
  (r : X -> Y)(c : (s : S) -> (T s -> Y) -> Y)
  (f : General S T X -> Y) ->
  ((x : X) ->                            f (!! x)    == r x) ->
  ((s : S)(k : T s -> General S T X) ->  f (s ?? k)  == c s (f o k)) ->
  f == foldG r c
foldGUnique r c f rf cf = ext help where
  help : (g : _) -> _
  help (!! x) = rf x
  help (s ?? k) =
    f (s ?? k) =! cf s k !> 
    c s (f o k) =! <^ c s ^> $$ ext (\ t -> help (k t)) !>
    c s (foldG r c o k) !!!
\end{code}
An immediate consequence is that |foldG|-ing the constructors gives the
identity.
\begin{code}
.foldGId : forall {S T X} -> foldG !! _??_ == id {_}{General S T X}
foldGId =
  foldG !! _??_ <! foldGUnique !! _??_ id (\ _ -> refl) (\ _ _ -> refl) !=
  id !!!
\end{code}

With a further induction, we can establish a fusion law for the special
case of operations, like |>>=|, which preserve |??|.
\begin{code}
.foldGFusion : forall {l S T X Y}{Z : Set l}
  (r : Y -> Z)(c : (s : S) -> (T s -> Z) -> Z)(f : X -> General S T Y) ->
  (foldG r c o foldG f _??_) == foldG (foldG r c o f) c
foldGFusion r c f = ext help  where
  help : (g : _) -> _
  help (!! x)    = refl
  help (s ?? k)  =
    c s (foldG r c o foldG f _??_ o k) =! <^ c s ^> $$ ext (\ t -> help (k t)) !>
    c s (foldG (foldG r c o f) c o k) !!!
\end{code}

Now we can establish the monad laws.
\begin{code}
.GeneralKLaws : forall {S T} -> KleisliLaws (GeneralK {S} {T})
GeneralKLaws = record
  { idLeft   = \ g -> ext \ a -> foldGId $$ <^ g a ^>
  ; idRight  = \ _ -> refl
  ; assoc    = \ f g h -> ext \ a ->
    h a >>= (f <-< g) <! foldGFusion f _??_ g $$ <^ h a ^> !=
    (h a >>= g) >>= f !!!
  } where open Kleisli GeneralK
\end{code}

Now, let us consider what it is to be a `monad morphism' in this
setting.  Given |Kleisli M| and |Kleisli N|, we should have a
mapping |m : forall {X} -> M X -> N X| such that |m o -|
respects |return| and |<-<|. \textbf{Is |m| natural? Yes, but
does that matter?}


\begin{code}
record KleisliMorphism
  {i j k}{M : Set i -> Set j}{N : Set i  -> Set k}
  (KM : Kleisli M)(KN : Kleisli N)(m : forall {X} -> M X -> N X)
  : Set (lsuc (i ⊔ j ⊔ k)) where
  module KMM = Kleisli KM
  module KNM = Kleisli KN
  field
    .respI  :  {X : Set i} -> (m o KMM.return {X}) == KNM.return {X}
    .respC  :  {A B C : Set i}(f : B -> M C)(g : A -> M B) ->
               (m o KMM._<-<_ f g) == KNM._<-<_ (m o f) (m o g)
\end{code}

\begin{code}
idIsMorph : forall {i j}{M : Set i -> Set j}(KM : Kleisli M) ->
  KleisliMorphism KM KM id
idIsMorph KM = record { respI = refl ; respC = \ _ _ -> refl }
\end{code}

\begin{code}
compMorph : forall {i j k l}
  {M : Set i -> Set j}{N : Set i -> Set k}{P : Set i -> Set l}
  (KM : Kleisli M)(KN : Kleisli N)(KP : Kleisli P)
  (m : forall {X} -> M X -> N X)(p : forall {X} -> P X -> M X) ->
  KleisliMorphism KM KN m -> KleisliMorphism KP KM p ->
  KleisliMorphism KP KN (m o p)
compMorph KM KN KP m p mn pm = record
  {  respI =
       (m o (p o P.return))             =! <^ _o_ m ^> $$ PM.respI !> 
       (m o (M.return))                 =! MN.respI !>
       N.return                         !!! 
  ;  respC = \ f g ->
       (m o (p o (f P.<-< g)))          =! <^ _o_ m ^> $$ PM.respC f g !>
       (m o ((p o f) M.<-< (p o g)))    =! MN.respC (p o f) (p o g) !>
       ((m o p o f) N.<-< (m o p o g))  !!!
  }  where
      open module MN = KleisliMorphism mn
      open module PM = KleisliMorphism pm
      open module P = Kleisli KP
      open module N = Kleisli KN
      open module M = Kleisli KM
\end{code}


\begin{code}
const : {l : Level}{X : Set l} -> X -> One -> X
const x <> = x

genMorph :  forall {l S T}{M : Set -> Set l} -> Kleisli M ->
            (h : (s : S) -> M (T s)) ->
            {X : Set} -> General S T X -> M X
genMorph KM h = foldG return (_>>=_ o h) where open Kleisli KM

genIsMorph :  forall {l S T}
              {M : Set -> Set l}(KM : Kleisli M)(KLM : KleisliLaws KM) ->
              (h : (s : S) -> M (T s)) ->
              KleisliMorphism (GeneralK {S}{T}) KM (genMorph KM h)
genIsMorph KM KLM h = record
  { respI  = refl
  ; respC  = \ f g -> ext (help f o g)
  } where
      open Kleisli KM ; open KleisliLaws KLM
      .help :  {B C : Set}(f : B -> General _ _ C)(b : General _ _ B) ->
               genMorph KM h (foldG f _??_ b) ==
               (genMorph KM h b >>= (genMorph KM h o f))
      help f (!! x) = genMorph KM h (f x)
         <! idRight (genMorph KM h o f) $$ <^ x ^> !=
        return x >>= (genMorph KM h o f) !!!
      help f (s ?? k) = (h s >>= (genMorph KM h o (foldG f _??_ o k))) =! <^ _>>=_ (h s) ^> $$ (ext \ t -> help f (k t)) !>
        (((genMorph KM h o f) <-< (genMorph KM h o k)) <-< const (h s)) <>
        =! assoc (genMorph KM h o f) (genMorph KM h o k) (const (h s)) $$ <^ <> ^> !>
       (h s >>= (genMorph KM h o k)) >>= (genMorph KM h o f) !!! 
\end{code}

\begin{code}
.morphIsFold :  forall {l S T}
               {M : Set -> Set l}(KM : Kleisli M)(KLM : KleisliLaws KM) ->
               (m : {X : Set} -> General S T X -> M X) ->
               KleisliMorphism (GeneralK {S}{T}) KM m ->
               {X : Set} -> m {X} == genMorph KM (m o call) {X}
morphIsFold KM KLM m mm {X} = ext help where
  open Kleisli ; open KleisliLaws KLM ; open KleisliMorphism mm
  help : (g : General _ _ _) -> _
  help (!! x) = respI $$ <^ x ^>
  help (s ?? k) =
    (m o (_<-<_ GeneralK k (const (call s)))) <>
       =! respC k (const (call s)) $$ <^ <> ^> !>
    (_>>=_ KM (m (call s)) (m o k))
       =! <^ _>>=_ KM (m (call s)) ^> $$ ext (\ t -> help (k t)) !>
    _>>=_ KM (m (call s)) (genMorph KM (m o call) o k) !!! 
\end{code}


\section{General Recursion with the General Monad}

%format PiG = "\F{PiG}"
If we build a request-response tree from individual |call|s, we give a
strategy for interacting with an oracle which responds to requests |s : S|
with values in |T s|. We may thus define |PiG|
\begin{code}
PiG : (S : Set)(T : S -> Set) -> Set
PiG S T = (s : S) -> General S T (T s)
\end{code}
to be a type of recursive \emph{strategies}
for computing a |T s| from some |s : S|.
These strategies are finite: they tell us how to expand one request in terms
of zero or more recursive calls.
%format expand = "\F{expand}"
\begin{code}
expand : forall {S T X} -> PiG S T -> General S T X -> General S T X
expand f = genMorph GeneralK f
\end{code}
%format gf = "\F{f}"
You will have noticed that |call : PiG S T|, and that |expand call| just
replaces one request with another, acting as the identity. As a recursive
strategy, taking |f = \ s -> call s| amounts to the often valid but seldom
helpful `definition':
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
...                      |     tt = !! start
...                      |     ff = call (step start)
\end{code}

For Turing machines,
|S| should pair a machine state with a tape, |stop| should
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
  engine (!! x)    _        = yes x
  engine (s ?? g)  zero     = no
  engine (s ?? g)  (suc n)  = engine (f s >G>= g) n
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

\textbf{Sized types fix it!}
Sadly, the following code fails Agda's rather syntactic productivity check.
%format unfold = "\F{unfold}"
%format help = "\F{help}"
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
or its continuation, instantiated with a given |x|.
%format D>= = >>=
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

Our request-response characterization of general recursion is readily
mapped onto |Delay|. The coalgebra of the |unfold| just expands the topmost
node of the call graph.
%format delay = "\F{delay}"
%format go = "\F{go}"
\begin{code}
delay : forall {S T}(f : PiG S T){X} -> General S T X -> Delay X
\end{code}
\begin{spec}
delay f = genMorph (record { return = Dret ; _>>=_ = _D>=_ })
   (\ s -> later (delay f (f s)))
\end{spec}
\begin{code}
delay {S}{T} f = unfold go where
  go : forall {X} -> General S T X -> X + (General S T X)
  go (!! t)    = inl t
  go (s ?? k)  = inr (f s >G>= k)
\end{code}


\section{Completely Iterative Monads}

The \emph{completely iterative} monad generated by a request-response system
is given by the possibly infinite request-response trees with values at whatever
leaves may be reachable. When we inspect the top of such a tree, we will find
either a leaf or the dependent pair of a request and its resumption.

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

CF : (S : Set)(T : S -> Set)(X Y : Set) -> Set
CF S T X Y = X + Sg S \ s -> T s -> Y 

record ComIt (S : Set)(T : S -> Set)(X : Set) : Set where
  coinductive
  constructor pack
  field
    top : CF S T X (ComIt S T X)
open ComIt

cret : forall {S T X} -> X -> ComIt S T X
top (cret x) = inl x

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
DELAY  :  Set -> Set
DELAY  =  ComIt One \ _ -> One

yield  :  One -> DELAY One
yield  _  = cocall <>
\end{code}

\begin{code}
data Zero : Set where

HEq : {S : Set}{T : S -> Set}{s s' : S}(q : s == s') -> T s -> T s' -> Set
HEq refl t t' = t == t'

module BISIM {S}{T}{X} where
  mutual
    record Bisim (p q : ComIt S T X) : Set where
      coinductive
      field
        step : Step Bisim (top p) (top q)

    Step : (R : ComIt S T X -> ComIt S T X -> Set)
           (p' q' : CF S T X (ComIt S T X)) -> Set
    Step R (inl x)        (inl x')         = x == x'
    Step R (inl _)        (inr _)          = Zero
    Step R (inr _)        (inl _)          = Zero
    Step R (inr (s , k))  (inr (s' , k'))  =
      Sg (s == s') \ q ->
      (t : T s)(t' : T s') -> HEq q t t' ->
      R (k t) (k' t')

  open Bisim

  bisim : (R : (p q : ComIt S T X) -> Set) ->
          ((p q : ComIt S T X) -> R p q -> Step R (top p) (top q)) ->
          {p q : ComIt S T X} -> R p q -> Bisim p q
  step (bisim R s {p} {q} r) = help (top p) (top q) (s p q r) where
    help : (p' q' : CF S T X (ComIt S T X)) ->
           Step R p' q' -> Step Bisim p' q'
    help (inl x) (inl y) z = z
    help (inl x) (inr y) z = z
    help (inr x) (inl y) z = z
    help (inr (x , k)) (inr (.x , k')) (refl , kq) =
      refl , (\ t t' tq -> bisim R s (kq t t' tq) )

  postulate
    .bisimEq : {p q : ComIt S T X} -> Bisim p q -> p == q

  .poke : {p q : ComIt S T X} -> top p == top q -> p == q
  poke pq = bisimEq (bisim (\ p q -> top p == top q)
    (\ p q -> help (top p) (top q)) pq) where
    help : (p' q' : CF S T X (ComIt S T X)) -> p' == q' ->
           Step  (\ p q -> top p == top q) p' q'
    help (inl x) ._ refl = refl
    help (inr (s , k)) ._ refl = refl , \ { t ._ refl -> refl }

open BISIM

COMIT : forall {S T} -> Kleisli (ComIt S T)
COMIT = record { return = cret ; _>>=_ = _C>=_ }

COMITLaws : forall {S T} -> KleisliLaws (COMIT {S}{T})
COMITLaws {S}{T} = record
  { idLeft   = \ g -> ext \ a -> bisimEq
      (bisim
       (\ p q -> p == (q C>= cret))
      (\ { .(q C>= cret) q refl -> idlHelp q }) refl )
  ; idRight  = \ f -> ext \ a -> bisimEq
    {!bisim (\ p q -> p ==!}
  ; assoc    = {!!}
  } where
  idlHelp : {X : Set}(q : ComIt S T X) ->
    Step (\ p q -> p == (q C>= cret)) (top (q C>= cret)) (top q)
  idlHelp q with top q 
  idlHelp q | inl x = refl
  idlHelp q | inr (s , k) = refl , (\ { t .t refl -> refl })
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


  IRK : Kleisli IR
  IRK = record { return = iota ; _>>=_ = _I>=_ } where
    _I>=_ : forall {X Y} -> IR X -> (X -> IR Y) -> IR Y
    iota x I>= K = K x
    sigma A T I>= K = sigma A \ a -> T a I>= K
    delta B s T I>= K = delta B s \ f -> T f I>= K

  IRKL : KleisliLaws IRK
  IRKL = record
    { idLeft = \ g -> ext (idl o g)
    ; idRight = \ f -> refl
    ; assoc = \ f g h -> ext (ass f g o h)
    } where
    open Kleisli IRK
    .idl : {X : Set}(T : IR X) -> (T >>= iota) == T
    idl (iota oo) = refl
    idl (sigma A T) = <^ sigma A ^> $$ ext \ a -> idl (T a)
    idl (delta B s T) = <^ delta B s ^> $$ ext \ f -> idl (T f)
    .ass : {B C D : Set}(f : C -> IR D)(g : B -> IR C) ->
          (T : IR B) -> (T >>= (f <-< g)) == ((T >>= g) >>= f)
    ass f g (iota oo) = refl
    ass f g (sigma A T) = <^ sigma A ^> $$ ext \ a -> ass f g (T a)
    ass f g (delta B s T) = <^ delta B s ^> $$ ext \ h -> ass f g (T h)
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
open module Yummy {S}{I} = IndRec.IndRecType {S} I
\end{code}



\section{The Bove-Capretta Construction}

\begin{code}
genIR : forall {S T X} -> General S T X -> IR T X
genIR = genMorph (IRK _) (\ s -> delta One (const s) \ t -> iota (t <>))

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

