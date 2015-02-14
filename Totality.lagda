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
  Size<_ : Size -> Set
  up : Size -> Size
  infty : Size
{-# BUILTIN SIZE Size #-}
{-# BUILTIN SIZELT Size<_ #-}
{-# BUILTIN SIZESUC up #-}
{-# BUILTIN SIZEINF infty #-}

_o_ : {i j k : Level}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : {a : A}(b : B a) -> C a b)(g : (a : A) -> B a) ->
  (a : A) -> C a (g a)
f o g = \ x -> f (g x)
infixr 3 _o_

data _==_ {l : Level}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
infixr 1 _==_

id : {l : Level}{X : Set l} -> X -> X
id x = x


record One {l} : Set l where constructor <>
const : {i l : Level}{X : Set l} -> X -> One {i} -> X
const x <> = x

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

%format -> = "\!\rightarrow\!"
%format forall = "\blue{\forall}"

%format (BROWN x) = "\brownBG{\ensuremath{" x "}}"

\title{Totality versus Turing-Completeness?}
\author{Conor McBride}
\institute
  {University of Strathclyde\\
   \email{conor@@strictlypositive.org}
  }

\begin{document}
\maketitle

\begin{abstract} In this literate Agda paper, I show that general
recursive definitions can be represented in the free monad which
supports the `effect' of making a recursive call, without saying
how these programs should be executed. Diverse semantics can be
given by suitable monad morphisms. The Bove-Capretta
construction of the domain of a general recursive function can be
presented datatype-generically as an instance of this technique.
\end{abstract}

\section{Introduction}

Advocates of Total Functional Programming~\cite{Turner04}, such as
myself, can prove prone to a false confession, namely that the price
of functions which function is the loss of Turing-completeness. In a
total language, to construct $f : S\to T$ is to promise a
canonical $T$ eventually, given a canonical $S$. The alleged benefit
of general recursion is just to inhibit such strong
promises. To make a weaker promise, simply construct a total function
of type $S\to G\:T$ where $G$ is a suitable monad.

The literature and lore of our discipline are littered with candidates
for $G$, and this article will contribute another---the \emph{free}
monad with one operation $f : S\to T$. To work in such a monad is to
\emph{write} a general recursive function without prejudice as to how
it might be \emph{executed}. We are then free, in the technical sense,
to choose any semantics for general recursion we like by giving a
suitable \emph{monad morphism} to another notion of partial
computation.  For example, Venanzio Capretta's partiality
monad~\cite{DBLP:journals/lmcs/Capretta05}, also known as the
\emph{completely iterative} monad on the operation
$\mathit{yield}:1\to 1$, which might never deliver a value, but
periodically offers its environment the choice of whether to interrupt
computation or to continue.

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
though the relevant programs---notably the language's own
evaluator---are total. Translated across the Curry-Howard
correspondence, the argument for general recursion asserts that
logical inconsistency is a price worth paying for logical
completeness, notwithstanding the loss of the language's value as
\emph{evidence}.  Programmers are free to maintain that such
dishonesty is essential to their capacity to earn a living, but a new
generation of programming technology enables some of us to offer and
deliver a higher standard of guarantee. \emph{Faites vos jeux!}


\section{The General Free Monad}

Working (\url{http://github.com/pigworker/Totality}), in Agda, we may
define a free monad which is general, both in the sense of being
generated by any strictly positive functor, and in the sense of being
suited to the modelling of general recursion.

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

|General| datatypes come with a catamorphism, or `fold'
operator.\footnote{Whenever I intend a monoidal
accumulation, I say `crush', not `fold'.}
%format foldG = "\F{fold}"
\begin{code}
foldG :  forall {l S T X}{Y : Set l} ->
         (X -> Y) -> ((s : S) -> (T s -> Y) -> Y) ->
         General S T X -> Y
foldG r c (!! x)    = r x
foldG r c (s ?? k)  = c s \ t -> foldG r c (k t)
\end{code}

The `bind' operation for the monad |General S T| substitutes
computations for values to build larger computations. It is, of course,
a |foldG|.

%format forall = "\mathkw{\forall}"
%format >>= = "\F{>\!\!>\!\!=}"
%format G>= = >>= "_{\D{G}}"
%format _G>=_ = _ G>= _
\begin{code}
_G>=_ :  forall {S T X Y} ->
         General S T X -> (X -> General S T Y) -> General S T Y
g G>= k  = foldG k _??_ g
infixl 4 _G>=_
\end{code}

We then acquire what Gordon Plotkin and John Power refer to as a
\emph{generic effect} \cite{DBLP:journals/acs/PlotkinP03}---the
presentation of an individual request-response interaction:
%format call = "\F{call}"
\begin{code}
call : forall {S T}(s : S) -> General S T (T s)
call s = s ?? !!
\end{code}

%format PiG = "\F{PiG}"
Now we may say how to give a recursive definition for a function.
For each argument |s : S|, we must build a request-response tree from
individual |call|s, ultimately delivering a value in |T s|.
We may thus define the `general recursive $\Uppi$-type',
\begin{code}
PiG : (S : Set)(T : S -> Set) -> Set
PiG S T = (s : S) -> General S T (T s)
\end{code}
to be a type of functions delivering the recursive \emph{strategy}
for computing a |T s| from some |s : S|.

%format Nat = "\D{Nat}"
%format zero = "\C{zero}"
%format suc = "\C{suc}"
For example, given the natural numbers,
\begin{code}
data Nat : Set where
  zero  : Nat
  suc   : Nat -> Nat
\end{code}
%if False
\begin{code}
{-# BUILTIN NATURAL Nat #-}
\end{code}
%endif
the following obfuscated identity function will not pass Agda's
syntactic check for guardedness of recursion.
%format fusc = "\F{fusc}"
\begin{spec}
(BROWN fusc) : Nat -> Nat
fusc zero     = zero
fusc (suc n)  = suc ((BROWN fusc) ((BROWN fusc) n))
\end{spec}
However, we can represent its definition without such controversy.
\begin{code}
fusc : PiG Nat \ _ -> Nat
fusc zero     =  !! zero
fusc (suc n)  =  call n G>= \ fn -> call fn  G>= \ ffn -> !! (suc ffn)
\end{code}
Each |call| is only a \emph{placeholder} for a recursive call to
|fusc|. The latter tells us just how to expand the recursion
\emph{once}. Note that |fusc|'s \emph{nested} recursive calls
make use of the way |G>=| allows values from earlier
effects to influence the choice of later effects. Using only a
free applicative functor would exactly exclude nested recursion.

Even so, it is fair to object that the `monadified' definition
is ugly compared to its direct but not obviously terminating
counterpart, with more intermediate naming. Monadic
programming is ugly in general, not just in |General|!  Languages like
Bauer and Pretnar's \emph{Eff}~\cite{DBLP:journals/jlp/BauerP15}
show us that we can solve
this problem, working in direct style for whatever effectful interface
is locally available, but meaning the computation delivered by the
appropriate Moggi-style translation into an explicitly monadic
kernel~\cite{DBLP:conf/lics/Moggi89}.
There is no need to
consider monadic style a just punishment, whatever your impurity.

By choosing the |General| monad, we have not committed to any notion
of `infinite computation'. Rather, we are free to work with a variety
of monads |M| which might represent the execution of a general
recursive function, by giving a \emph{monad morphism} from |General S
T| to |M|, mapping each request to something which tries to deliver
its response.  Correspondingly, we shall need to define these concepts
more formally.


\section{Monads and Monad Morphisms, More or Less}

This section is a formalisation of material which is largely standard.
The reader familiar with monad morphisms should feel free to skim for
notation without fear of missing significant developments.

%format Kleisli = "\D{Kleisli}"
Let us introduce the notion of a |Kleisli| structure on sets,
as Altenkirch and Reus called it, known to Altenkirch, Chapman and
Uustalu as a `relative' monad~\cite{DBLP:conf/csl/AltenkirchR99,DBLP:conf/fossacs/AltenkirchCU10}.
%format ⊔ = "\F{\sqcup}"
%format return = "\F{return}"
%format _>>=_ = _ >>= _
%format lsuc = "\C{lsuc}"
%format lzero = "\C{lzero}"
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
  _<-<_ :  forall {A B C : Set i} ->
           (B -> M C) -> (A -> M B) -> (A -> M C)
  (f <-< g) a = g a >>= f
  infixl 4 _>>=_ _<-<_
\end{code}
Although the `notion of computation'
is given by a mapping on value sets, that mapping need not be an
\emph{endofunctor}. We shall later find use for this
flexibility when we interpret small computations as large descriptions
of datatypes. The upshot is that we are obliged to work polymorphically
in our set-theoretic magnitude.
Given the fields |return| and |>>=|,
we may equip ourselves with Kleisli composition in the
usual way, replacing each value emerging from |g| with
the computation indicated by |f|. Of course, we have
%format GeneralK = "\F{GeneralK}"
\begin{code}
GeneralK : forall {S T} -> Kleisli (General S T)
GeneralK = record { return = !! ; _>>=_ = _G>=_ }
\end{code}

%format == = "\mathrel{\D{\equiv}}"
%format refl = "\C{refl}"
%format !!! = "\F{\square}"
%format _!!! = "\F{\_}" !!!
%format =! = "\F{=\!\![}"
%format !> = "\F{\rangle\!\!=}"
%format != = "\F{]\!\!=}"
%format <! = "\F{=\!\!\langle}"
%format _=!_!>_ = "\F{\_}" =! "\F{\_}" !> "\F{\_}"
%format _<!_!=_ = "\F{\_}" <! "\F{\_}" != "\F{\_}"
%format =$= = "\F{=\!\!\!\!\$\!\!\!\!=}"
%format _=$=_ = _ =$= _
%format <^ = "\F{\lceil}\!"
%format ^> = "\!\F{\rceil}"
%format <^_^> = <^ _ ^>
%format ext = "\F{ext}"
%format .ext = "." ext
\newcommand{\postext}{
\begin{code}
postulate
  .ext :  forall  {i j}{A : Set i}{B : A -> Set j}{f g : (a : A) -> B a} ->
                    ((a : A) -> f a == g a) -> f == g
\end{code}}
\newcommand{\rewtools}{
\begin{code}
_=!_!>_ : forall {l}{X : Set l}(x : X){y z} -> x == y -> y == z -> x == z
x =! refl !> q = q

_<!_!=_ : forall {l}{X : Set l}(x : X){y z} -> y == x -> y == z -> x == z
x <! refl != q = q

_!!! : forall {l}{X : Set l}(x : X) -> x == x
x !!! = refl
infixr 2 _!!! _=!_!>_ _<!_!=_
\end{code}}
\newcommand{\apptools}{
\begin{code}
<^_^> :  forall {l}{X : Set l}(x : X) -> x == x
<^ x ^> = refl

_=$=_ :  forall {i j}{S : Set i}{T : Set j}{f g : S -> T}{x y : S} ->
         f == g -> x == y -> f x == g y
refl =$= refl = refl

infixl 9 _=$=_
\end{code}}

The `Monad laws' amount to
requiring that |return| and |<-<| give us a category.
\begin{code}
record KleisliLaws {i j}{M : Set i -> Set j}(KM : Kleisli M)
  : Set (lsuc (i ⊔ j)) where
  open Kleisli KM
  field
    .idLeft    : forall  {A B}(g : A -> M B) ->  return <-< g  ==  g
    .idRight   : forall  {A B}(f : A -> M B) ->  f <-< return  ==  f
    .assoc     : forall  {A B C D}
                         (f : C -> M D)(g : B -> M C)(h : A -> M B) ->
                                                 (f <-< g) <-< h == f <-< (g <-< h)
\end{code}
The dots before the field names make those fields
unavailable for computational purposes. Correspondingly, I have little
compunction about postulating an extensional equality and reasoning
by transforming functions.
\postext

In order to improve the readability of proofs, I expose the
reflexivity, symmetry and transitivity of equality in a way that lets
us show our steps.
\rewtools

I also make use of the way applicative forms respect equality.
\apptools
E.g., we may show that the usual law for iterating |>>=| is basically associativity.
%format const = "\F{const}"
%format <> = "\C{\langle\rangle}"
%format binds = "\F{binds}"
%format .binds = "." binds
\begin{code}
  .binds : forall {A B C}(a : M A)(f : B -> M C)(g : A -> M B) ->
             a >>= (f <-< g) == a >>= g >>= f
  binds a f g = assoc f g (const a) =$= <^ <> ^>
\end{code}

Let us warm up to the proofs of the |KleisliLaws| with some basic
properties of |foldG|. Firstly, anything satisfying
the defining equations of a |foldG| is a |foldG|.
%format foldGUnique = "\F{foldUnique}"
%format .foldGUnique = "." foldGUnique
%format help = "\F{help}"
\begin{code}
.foldGUnique : forall {l S T X}{Y : Set l}(f : General S T X -> Y) r c ->
  (forall x ->    f (!! x)    == r x          ) -> (forall s k ->  f (s ?? k)  == c s (f o k)  ) ->
  f == foldG r c
foldGUnique f r c rq cq = ext help where
  help : (g : _) -> _
  help (!! x)    =  f (!! x) =! rq x !> r x !!!
  help (s ?? k)  =  f (s ?? k)           =! cq s k !> 
                    c s (f o k)          =! <^ c s ^> =$= ext (\ t -> help (k t)) !>
                    c s (foldG r c o k)  !!!
\end{code}
An immediate consequence is that |foldG|-ing the constructors gives the
identity.
%format foldGId = "\F{foldId}"
%format .foldGId = "." foldGId
\begin{code}
.foldGId : forall {S T X} -> foldG !! _??_ == id {_}{General S T X}
foldGId =  foldG !! _??_  <! foldGUnique id !! _??_ (\ _ -> refl) (\ _ _ -> refl) !=
           id             !!!
\end{code}

With a further induction, we can establish a fusion law for |foldG| after
|>>=|.
%format foldGFusion = "\F{foldFusion}"
%format .foldGFusion = "." foldGFusion
\begin{code}
.foldGFusion : forall {l S T X Y}{Z : Set l}
  (r : Y -> Z)(c : (s : S) -> (T s -> Z) -> Z)(f : X -> General S T Y) ->
  (foldG r c o foldG f _??_) == foldG (foldG r c o f) c
foldGFusion r c f = ext help  where
  help : (g : _) -> _
  help (!! x)    = refl
  help (s ?? k)  =
    c s (foldG r c o foldG f _??_ o k)  =! <^ c s ^> =$= ext (\ t -> help (k t)) !>
    c s (foldG (foldG r c o f) c o k)   !!!
\end{code}
That is enough to establish the |KleisliLaws| for |GeneralK|.
%format GeneralKLaws = "\F{GeneralKLaws}"
%format .GeneralKLaws = "." GeneralKLaws
\begin{code}
.GeneralKLaws : forall {S T} -> KleisliLaws (GeneralK {S} {T})
GeneralKLaws = record
  { idLeft   = \ g -> <^ (\ k -> k o g) ^> =$= foldGId  ; idRight  = \ _ -> refl
  ; assoc    = \ f g h ->
      (f <-< g) <-< h  <! <^ (\ k -> k o h) ^> =$= foldGFusion f _??_ g !=
      f <-< (g <-< h)  !!!
  } where open Kleisli GeneralK
\end{code}

Now, let us consider when a polymorphic function |m : forall
{X} -> M X -> N X| is a \emph{monad morphism} in this setting.
Given |Kleisli M| and |Kleisli N|, |m o -| should map
|return| and |<-<| from |M| to |N|.
%format KleisliMorphism = "\D{Morphism}"
%format KMM = "-_{" M "}"
%format KGM = "-_{\D{G}}"
%format KNM = "-_{" N "}"
%format KMM.return = return "_{" M "}"
%format KNM.return = return "_{" N "}"
%format KMM.<-< = <-< "_{" M "}"
%format KGM.<-< = <-< "_{\D{G}}"
%format KMM._>>=_ = _ >>= "_{" M "}" _
%format KMM.>>= = >>= "_{" M "}"
%format KNM.<-< = <-< "_{" N "}"
%format respI = "\F{respI}"
%format respC = "\F{respC}"
%format .respI = "." respI
%format .respC = "." respC
\begin{code}
record KleisliMorphism  {i j k}{M : Set i -> Set j}{N : Set i  -> Set k}
                        (KM : Kleisli M)(KN : Kleisli N)
  (m : forall {X} -> M X -> N X) : Set (lsuc (i ⊔ j ⊔ k)) where
  module KMM = Kleisli KM ; module KNM = Kleisli KN
  field
    .respI  :  {X : Set i} ->
                  m o KMM.return {X} == KNM.return {X}
    .respC  :  {A B C : Set i}(f : B -> M C)(g : A -> M B) ->
                  m o (f KMM.<-< g) == (m o f) KNM.<-< (m o g)
\end{code}

%format idMorph = "\F{idMorph}"
%format compMorph = "\F{compMorph}"
The proofs, |idMorph| and |compMorph|,
that monad morphisms are closed under identity and composition,
are left as straightforward exercises for the reader.
%if False
\begin{code}
idMorph : forall {i j}{M : Set i -> Set j}(KM : Kleisli M) ->
  KleisliMorphism KM KM id
idMorph KM = record { respI = refl ; respC = \ _ _ -> refl }
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
       (m o (p o P.return))             =! <^ _o_ m ^> =$= PM.respI !> 
       (m o (M.return))                 =! MN.respI !>
       N.return                         !!! 
  ;  respC = \ f g ->
       (m o (p o (f P.<-< g)))          =! <^ _o_ m ^> =$= PM.respC f g !>
       (m o ((p o f) M.<-< (p o g)))    =! MN.respC (p o f) (p o g) !>
       ((m o p o f) N.<-< (m o p o g))  !!!
  }  where
      open module MN = KleisliMorphism mn
      open module PM = KleisliMorphism pm
      open module P = Kleisli KP
      open module N = Kleisli KN
      open module M = Kleisli KM
\end{code}
%endif

%format Sg = "\D{\Upsigma}"
%format , = "\C{,}\:"
%format fst = "\F{fst}"
%format snd = "\F{snd}"
%format constructor = "\mathkw{constructor}"
Now, |General S T| is the free monad on the functor
|Sg S \ s -> T s -> -| which captures a single request-response
interaction. It is a free construction, turning functors into monads,
in the sense that it is left adjoint to the forgetful map which turns
monads back into functors. In other words, the monad morphisms from a
free monad to |M| are exactly given by the polymorphic functions from the
underlying functor to |M|. In our case, the monad morphisms
\[
  |m : forall {X} -> General S T X -> M X|
\]
are given exactly by the functions of type
\[\begin{array}{rl}
  |forall {X} -> (Sg S \ s -> T s -> X) -> M X|
\cong \\
  |(s : S) -> forall {X} -> (T s -> X) -> M X|
\cong &
  |(s : S) -> M (T s)|
\end{array}\]
That is, the monad morphisms from |General S T| to |M| are exactly
given by the `|M|-acting versions' of our function.
%format morph = "\F{morph}"
\begin{code}
morph :  forall  {l S T}{M : Set -> Set l}(KM : Kleisli M)
                 (h : (s : S) -> M (T s))
                 {X} -> General S T X -> M X
morph KM h = foldG return (_>>=_ o h) where open Kleisli KM
\end{code}

%format morphFusion = "\F{morphFusion}"
%format .morphFusion = "." morphFusion
\newcommand{\morphFusion}{
\begin{code}
.morphFusion : forall  {l S T X Y}
  {M : Set -> Set l}(KM : Kleisli M)(KLM : KleisliLaws KM)
  (f : X -> M Y)(h : (s : S) -> M (T s)) ->
  let open Kleisli KM in
    f <-< morph KM h == foldG {_}{S}{T} f (_>>=_ o h)
morphFusion KM KLM f h = ext help where
  open Kleisli KM ; open KleisliLaws KLM
  help : (g : _) -> _
  help (!! x)    =  (f <-< return) x  =! idRight f =$= <^ x ^> !> f x !!!
  help (s ?? k)  =  (f <-< morph KM h) (s ?? k)
    =! refl !>      h s >>= (morph KM h o k) >>= f
    <! binds (h s) f (morph KM h o k) !=
                    h s >>= (f <-< (morph KM h o k))
    =! <^ _>>=_ (h s) ^> =$= ext (\ t -> help (k t)) !>
                    foldG f (_>>=_ o h) (s ?? k)      !!! 
\end{code}}

Let us show that |morph| makes |KleisliMorphism|s.
%format morphMorphism = "\F{morphMorphism}"
\begin{code}
morphMorphism :  forall {l S T}{M : Set -> Set l}
  (KM : Kleisli M)(KLM : KleisliLaws KM) ->
  (h : (s : S) -> M (T s)) ->
  KleisliMorphism (GeneralK {S}{T}) KM (morph KM h)
morphMorphism {_}{S}{T} KM KLM h =
  let  module KGM  = Kleisli (GeneralK {S} {T})
       module KMM  = Kleisli KM ; open KleisliLaws KLM
  in   record
    { respI  = refl
    ; respC  = \ f g ->  morph KM h o (f KGM.<-< g) =! refl !>
                         foldG KMM.return (KMM._>>=_ o h) o foldG f _??_ o g
        =!  <^ (\ k -> k o g) ^>  =$= (
\end{code}
Expanding |KGM.<-<| and focusing our attention before
the |o g|, we find a fusion opportunity.
\begin{code}
                                  foldG KMM.return (KMM._>>=_ o h) o foldG f _??_
            =! foldGFusion KMM.return (KMM._>>=_ o h) f !>
                                  foldG (morph KM h o f) (KMM._>>=_ o h)
            <! morphFusion KM KLM (morph KM h o f) h !=
                                  (morph KM h o f) KMM.<-< morph KM h !!!
\end{code}
We find that |foldGFusion| leaves us with an operation which is almost
the definition |morph KM h|, except that where we want
|foldG KMM.return|, we have |foldG| of something else which we ought to be
able to move after the |foldG| by another fusion law, to be established forthwith. Meanwhile, plugging the |o g| back on the right, we are done.
\begin{code}
            ) !>         (morph KM h o f) KMM.<-< (morph KM h o g) !!! }
\end{code}

The lemma we need allows us to fuse any |f KMM.<-< morph KM h| into a
single |foldG|.
\morphFusion

Let us check that |morph| give us the \emph{only} monad morphisms from
|General S T|, using the uniqueness of |foldG|.
%format MM = "-_{" m "}"
%format MM.respI = respI "_{" m "}"
%format MM.respC = respC "_{" m "}"
%format morphOnly = "\F{morphOnly}"
%format .morphOnly = "." morphOnly
\begin{code}
.morphOnly :  forall {l S T}
   {M : Set -> Set l}(KM : Kleisli M)(KLM : KleisliLaws KM) ->
   (m : {X : Set} -> General S T X -> M X) -> KleisliMorphism GeneralK KM m ->
   {X : Set} -> m {X} == morph KM (m o call) {X}
morphOnly KM KLM m mm = foldGUnique m KMM.return (KMM._>>=_ o m o call)
  (\ x ->    m (!! x) =! MM.respI =$= <^ x ^> !> KMM.return x !!!)
  (\ s k ->  m (s ?? k)                           =! refl !>
             (m o (k KGM.<-< const (call s))) <>  =! MM.respC k (const (call s)) =$= <^ <> ^> !>
             m (call s) KMM.>>= (m o k)           !!!) 
  where
    module KGM  = Kleisli GeneralK
    module KMM  = Kleisli KM ; open KleisliLaws KLM 
    module MM   = KleisliMorphism mm
\end{code}


\section{General Recursion with the General Monad}

|General| strategies are finite: they tell us how to expand one request
in terms of a bounded number recursive calls. The operation which expands
each such request is a monad endomorphism---exactly the one generated by
our |f : PiG S T| itself, replacing each |call s| node in the tree by
the whole tree given by |f s|.
%format expand = "\F{expand}"
\begin{code}
expand : forall {S T X} -> PiG S T -> General S T X -> General S T X
expand f = morph GeneralK f
\end{code}
%format gf = "\F{f}"
You will have noticed that |call : PiG S T|, and that |expand call| just
replaces one request with another, acting as the identity. As a recursive
strategy, taking |f = \ s -> call s| amounts to the often valid but seldom
helpful `definition':
\[
  |gf s = gf s|
\]

By way of example, let us consider the evolution of state machines. We
shall need Boolean values:
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
Now let us construct the method for computing the halting state of a
machine, given its initial state and its one-step transition function.
%format halting = "\F{halting}"
\begin{code}
halting : forall {S} -> (S -> Bool) -> (S -> S) -> PiG S \ _ -> S
halting stop step start  with  stop start
...                      |     tt = !! start
...                      |     ff = call (step start)
\end{code}

For Turing machines, |S| should pair a machine state with a tape,
|stop| should check if the machine state is halting, and |step| should
look up the current state and tape-symbol in the machine description
then return the next state and tape. We can clearly explain how any
old Turing machine computes without stepping beyond the confines of
total programming, and without making any rash promises about what
values such a computation might deliver.


\section{The Petrol-Driven Semantics}

It is one thing to describe a general-recursive computation but quite
another to perform it. A simple way to give an arbitrary total
approximation to partial computation is to provide an engine which
consumes one unit of petrol for each recursive call it performs, then
specify the initial fuel supply. The resulting program is primitive
recursive, but makes no promise to deliver a value. Let us construct
it as a monad morphism. We shall need the usual model of \emph{finite}
failure, allowing us to give up when we are out of fuel.
%format Maybe = "\D{Maybe}"
%format yes = "\C{yes}"
%format no = "\C{no}"
%format petrol = "\F{petrol}"
%format engine = "\F{engine}"
%format MaybeK = "\F{MaybeK}"
%format MaybeKL = "\F{MaybeKL}"
\begin{code}
data Maybe (X : Set) : Set where
  yes  : X -> Maybe X
  no   : Maybe X
\end{code}

|Maybe| is monadic in the usual failure-propagating way.
\begin{code}
MaybeK : Kleisli Maybe
MaybeK = record  {  return  = yes
                 ;  _>>=_   = \ { (yes a) k -> k a ; no k -> no } }
\end{code}

The proof |MaybeKL : KleisliLaws MaybeK| is a matter of elementary
case analysis, so let us not dwell on it.
%if False
\begin{code}
MaybeKL : KleisliLaws MaybeK
MaybeKL = record
  {  idLeft   = \ g -> ext \ a -> idl (g a)
  ;  idRight  = \ f -> refl
  ;  assoc    = \ t s h -> ext \ a -> ass (h a) t s } where
  open Kleisli MaybeK
  idl : {A : Set}(ma : Maybe A) -> ma >>= yes == ma
  idl (yes s)  = refl
  idl no       = refl
  ass : {A B C : Set}(ma : Maybe A)(f : B -> Maybe C)(g : A -> Maybe B) ->
        ma >>= (f <-< g) == ma >>= g >>= f
  ass (yes a)  f g = refl
  ass no       f g = refl
\end{code}
%endif

We may directly construct the monad morphism which executes a general
recursion impatiently.
%format already = "\F{already}"
\begin{code}
already : forall {S T X} -> General S T X -> Maybe X
already = morph MaybeK \ s -> no
\end{code}
%format penguin = "\F{engine}"
%format petrol = "\F{petrol}"
That is, |!!| becomes |yes| and |??| becomes |no|, so the recursion
delivers a value only if it has terminated already. Now, if we have
some petrol, we can run an |penguin| which |expand|s the recursion for
a while, beforehand.
\begin{code}
penguin : forall {S T}(f : PiG S T)(n : Nat) {X} -> General S T X -> General S T X
penguin f zero     = id
penguin f (suc n)  = penguin f n o expand f
\end{code}
We obtain the petrol-driven (or step-indexed, if you prefer) semantics
by composition.

\begin{code}
petrol : forall {S T} -> PiG S T -> Nat -> (s : S) -> Maybe (T s)
petrol f n = already o penguin f n o f
\end{code}

If we consider |Nat| with the usual order and |Maybe X| ordered by
|no < yes x|, we can readily check that |petrol f n s| is monotone in |n|:
supplying more fuel can only (but sadly not strictly) increase the risk of
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

Whilst we are discussing the semanticses of total languages, it is
worth remembering that we expect dependently typed languages to come
with at least \emph{two}: a run time execution semantics which
computes only with closed terms, and an evaluation semantics which the
typechecker applies to open terms. It is quite normal for general
recursive languages to have a total typechecking algorithm.


\section{Capretta's Coinductive Semantics, via Abel and Chapman}

Coinduction in dependent type theory remains a vexed issue: we are
gradually making progress towards a presentation of productive
programming for infinite data structures, but we can certainly not
claim that we have a presentation which combines honesty, convenience
and compositionality. The state of the art is the current Agda
account due to Andreas Abel and colleagues, based on the notion of
\emph{copatterns}~\cite{DBLP:conf/popl/AbelPTS13} which allow us to
define lazy data by specifying observations of them, and on
\emph{sized types}~\cite{DBLP:phd/de/Abel2007} which give a more flexible
semantic account of productivity at the cost of additional indexing.

%format Delay = "\D{Delay}"
%format Delayter = "\D{Delay}^{\D{\infty}}"
%format force = "\F{force}"
%format now = "\C{now}"
%format later = "\C{later}"
%format coinductive = "\mathkw{coinductive}"
Abel and Chapman~\cite{DBLP:journals/corr/AbelC14} give a development
of normalization for simply typed |\|-calculus, using Capretta's |Delay|
monad~\cite{DBLP:journals/lmcs/Capretta05}
as a showcase for copatterns and sized types.
I will follow their setup, then construct a monad morphism from
|General|. The essence of their method is to define |Delay| as the
data type of \emph{observations} of lazy computations,
mutually with the record type, |Delayter|, of those lazy
computations themselves.
%format Size = "\D{Size}"
%format Size< = "\D{Size<}"
%format <* = "\C{\langle}\!"
%format *> = "\!\C{\rangle}"
%format <*_*> = <* _ *>
\begin{code}
mutual
  data Delay (i : Size)(X : Set) : Set where
    now    : X             -> Delay i X
    later  : Delayter i X  -> Delay i X
  record Delayter (i : Size)(X : Set) : Set where
    coinductive ; constructor <*_*>
    field force : {j : Size< i} -> Delay j X
open Delayter
\end{code}
%format + = "\D{+}"
%format _+_ = _ + _
%format inl = "\C{inl}"
%format inr = "\C{inr}"
%format unfold = "\F{unfold}"
%format unfolder = "\F{unfold}^{\F{\infty}}"
Abel explains that |Size|, here, characterizes the
\emph{observation depth} to which one may iteratively |force| the lazy
computation. Corecursive calls must reduce this depth, so cannot be
used for the topmost observation. Pleasingly, they need not be
rigidly guarded by constructors, because their sized types document
their legitimate use. For example, we may define the \emph{anamorphism},
or |unfold|, constructing a |Delay X| from a coalgebra for the
underlying functor |X + -|.
\begin{code}
data _+_ (S T : Set) : Set where
  inl  : S -> S + T
  inr  : T -> S + T
\end{code}
\begin{code}
[_,_] : {S T X : Set} -> (S -> X) -> (T -> X) -> S + T -> X
[ f , g ] (inl s) = f s
[ f , g ] (inr t) = g t

mutual
  unfold    : forall {i X Y} -> (Y -> X + Y) -> Y -> Delay i X
  unfold f y = [ now , later o unfolder f ] (f y)

  unfolder  : forall {i X Y} -> (Y -> X + Y) -> Y -> Delayter i X
  force (unfolder f y) = unfold f y
\end{code}

Based on projection, copatterns favours products over sum, which is
why most of the motivating examples are based on streams.  As soon as
we have a choice, mutual recursion becomes hard to avoid.  Thus
equipped, we can build a |Delay X| value by stepping a computation
which can choose either to deliver an |X| or to continue.


%format D>= = >>= "_{\D{D}}"
%format _D>=_ = _ D>= _
%format D>=& = >>= "^{\F{\infty}}_{\D{D}}"
%format _D>=&_ = _ D>=& _

Capretta explored the use of |Delay| as a monad to model general
recursion, with the |>>=| operator concatenating sequences of |later|s.
By way of example, he gives an interpretation of the classic language
with an operator seeking the minimum number satisfying a test.
Let us therefore equip |Delay| with a |>>=| operator. It can be
given as an |unfold|, but the direct definition with sized types
is more straightforward. Abel and Chapman give us the following
definition.
\begin{code}
mutual
  _D>=_ :    forall {i A B} ->
             Delay i A -> (A -> Delay i B) -> Delay i B
  now a     D>= f = f a
  later a'  D>= f = later (a' D>=& f)
  _D>=&_ :   forall {i A B} ->
             Delayter i A -> (A -> Delay i B) -> Delayter i B
  force (a' D>=& f) = force a' D>= f
\end{code}
and hence our purpose will be served by taking
%format DelayK = "\F{DelayK}"
\begin{code}
DelayK : {i : Size} -> Kleisli (Delay i)
DelayK = record { return = now ; _>>=_ = _D>=_ }
\end{code}
Abel and Chapman go further and demonstrate that these definitions
satisfy the monad laws up to strong bisimilarity, which is the
appropriate notion of equality for coinductive data but sadly not
the propositional equality which Agda makes available. I shall not
recapitulate their proof.

%format Nu = "\D{\upnu}"
%format One = "\D{1}"
%format * = "\D{\times}"
It is worth noting that the |Delay| monad is an example of a
\emph{completely iterative} monad, a final coalgebra
|Nu Y. X + F Y|, where the free monad, |General|, is an initial
algebra~\cite{DBLP:journals/entcs/GhaniLMP01}.
For |Delay|, take |F Y = Y|, or isomorphically,
|F Y = One * One -> Y|, representing a trivial request-response
interaction. That is |Delay| represents processes which must always
eventually \emph{yield}, allowing their environment the choice of
whether or not to resume them. We have at least promised to obey control-C!

By way of connecting the Capretta semantics with the petrol-driven variety,
we may equip every |Delay| process with a monotonic |engine|.
%format engine = "\F{engine}"
\begin{code}
engine : Nat -> forall {X} -> Delay _ X -> Maybe X
engine _        (now x)    = yes x
engine zero     (later _)  = no
engine (suc n)  (later d)  = engine n (force d)
\end{code}
Note that |engine n| is not a monad morphism unless |n| is |zero|.
\[\begin{array}{lcr}
 |engine 1 (later <* now tt *> >>= \ v -> later <* now v *>)| & = & |no| \\
 |engine 1 (later <* now tt *>) >>= \ v -> engine 1 (later <* now v *>)| & = &  |yes tt|
\end{array}\]

%format tryMorePetrol = "\F{tryMorePetrol}"
%format try = "\F{try}"
%format minimize = "\F{minimize}"
Meanwhile, given a petrol-driven process, we can just keep trying more and
more fuel. This is one easy way to write the minimization operator.
\begin{code}
tryMorePetrol : forall {i X} -> (Nat -> Maybe X) -> Delay i X
tryMorePetrol {_}{X} f = unfold try zero where
  try : Nat -> X + Nat
  try n  with  f n
  ...    |     yes x  = inl x
  ...    |     no     = inr (suc n)

minimize : (Nat -> Bool) -> Delay _ Nat
minimize test = tryMorePetrol \ n -> if test n then yes n else no
\end{code}

Our request-response characterization of general recursion is readily
mapped onto |Delay|. Sized types allow us to give the monad morphism
directly, corecursively interpreting each recursive |call|.
%format delay = "\F{delay}"
%format delayter = "\F{delay}^{\F{\infty}}"
%format go = "\F{go}"
\begin{code}
mutual
  delay     : forall {i S T}(f : PiG S T){X} -> General S T X -> Delay i X
  delay f = morph DelayK \ s -> later (delayter f (f s))
  delayter  : forall {i S T}(f : PiG S T){X} -> General S T X -> Delayter i X
  force (delayter f g) = delay f g
\end{code}
We can now transform our |General| functions
into their coinductive counterparts.
%format lazy = "\F{lazy}"
\begin{code}
lazy : forall {S T} -> PiG S T -> (s : S) -> Delay _ (T s)
lazy f = delay f o f
\end{code}


\section{A Little |\|-Calculus}

By way of a worked example, let us implement the untyped |\|-calculus.
We can equip ourselves with de Bruijn-indexed terms in the usual way.
I have taken the liberty of parametrizing these terms by a type of
inert constants |X|
%format Fin = "\D{Fin}"
%format Lam = "\D{\Uplambda}"
%format con = "\C{\upkappa}"
%format var = "\C{\#}"
%format lam = "\C{\uplambda}"
%format $ = "\C{\$}"
%format _$_ = _ $ _
\begin{code}
data Fin : Nat -> Set where
  zero  : {n : Nat} -> Fin (suc n)
  suc   : {n : Nat} -> Fin n -> Fin (suc n)

data Lam (X : Set)(n : Nat) : Set where
  con  : X -> Lam X n
  var  : Fin n -> Lam X n
  lam  : Lam X (suc n) -> Lam X n
  _$_  : Lam X n -> Lam X n -> Lam X n
infixl 5 _$_
\end{code}

In order to evaluate terms, we shall need a suitable notion of environment.
Let us make sure they have the correct size to enable projection.
%format Vec = "\D{Vec}"
%format / = "\!\C{\raisebox{ -0.07in}{\textrm{`}}}"
%format _/_ = _ / _
%format proj = "\F{proj}"
%format gam = "\V{\gamma}"
\begin{code}
data Vec (X : Set) : Nat -> Set where
  <>   : Vec X zero
  _/_  : {n : Nat} -> Vec X n -> X -> Vec X (suc n)

proj : forall {X n} -> Vec X n -> Fin n -> X
proj (_ / x)    zero     = x
proj (gam / _)  (suc n)  = proj gam n
\end{code}
Correspondingly, a \emph{value} is either a constant applied to
other values, or a function which has got stuck for want of its argument.
%format Val = "\D{Val}"
\begin{code}
data Val (X : Set) : Set where
  con : X -> {n : Nat} -> Vec (Val X) n -> Val X
  lam : {n : Nat} -> Vec (Val X) n -> Lam X (suc n) -> Val X
\end{code}

Now, in general, we will need to evaluate \emph{closures}---open
terms in environments.
%format Closure = "\D{Closure}"
%format & = "\C{\vdash}"
%format _&_ = _ & _
\begin{code}
data Closure (X : Set) : Set where
  _&_ : {n : Nat} -> Vec (Val X) n -> Lam X n -> Closure X
infixr 4 _&_
\end{code}

%format </ = "\F{\llbracket}"
%format /> = "\F{\rrbracket}"
%format </_/> = </ _ />
%format del = "\V{\delta}"
%format run = "\F{run}"
We can now give the evaluator, |</_/>| as a |General| recursive strategy to
compute a value from a closure. Application is the fun case. When
evaluating the argument and the function---subterms of the
application---we may use |</_/>| itself, rather than |call|. However,
when a $\beta$-redex starts a further evaluation, |call| is called for.
\begin{code}
</_/> : {X : Set} -> PiG (Closure X) \ _ -> Val X
</ gam & con x  />   = !! (con x <>)
</ gam & var i  />   = !! (proj gam i)
</ gam & lam b  />   = !! (lam gam b)
</ gam & f $ s  />   =
  </ gam & s /> G>= \ v -> </ gam & f /> G>= \  {
    (con x vs)   ->  !! (con x (vs / v))        ;
    (lam del b)  ->  call (del / v & b)         }
\end{code}

Thus equipped, |lazy </_/>| is the |Delay|ed version. Abel and
Chapman give a |Delay|ed interpreter (for typed terms)
directly, exercising some craft in negotiating size and mutual
recursion~\cite{DBLP:journals/corr/AbelC14}.
The |General| construction makes that craft systematic.


\section{An Introduction or Reimmersion in Induction-Recursion}

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

I have one more semantics for general recursion to show you,
constructing for any given |f : PiG S T| its \emph{domain}. The domain
is an inductively defined predicate, classifying the arguments which
give rise to call trees whose paths are finite. As Ana Bove observed,
the fact that a function is defined on its domain is a structural
recursion---the tricky part is to show that the domain predicate
holds~\cite{bove:njc}.  However, to support nested recursion, we need
to define the domain predicate and the resulting output
\emph{mutually}. Bove and Capretta realised that such mutual
definitions are just what we get from Dybjer and Setzer's notion of
\emph{induction-recursion}~\cite{DBLP:conf/tphol/BoveC01,DBLP:conf/dagstuhl/DybjerS01},
giving rise to the `Bove-Capretta method' of modelling general
recursion and generating termination proof obligations.

We can make the Bove-Capretta method generic, via the universe encoding
for (indexed) inductive-recursive sets presented by Dybjer and Setzer.
The idea is that each node of data is a record with some ordinary
fields coded by |sigma|, and some places for recursive
substructures coded by |delta|, with |iota| coding the end.
\begin{code}
data IR {l}{S : Set}(I : S -> Set l)(O : Set l) : Set (l ⊔ lsuc lzero) where
  iota   :  (oo : O)                                  -> IR I O
  sigma  :  (A : Set)(T : A -> IR I O)                -> IR I O
  delta  :  (B : Set)(s : B -> S)
            (T : (i : (b : B) -> I (s b)) -> IR I O)  -> IR I O
\end{code}
Now, in the indexed setting, we have |S| sorts of recursive substructure,
and for each |s : S|, we know that an `input' substructure can be
interpreted as a value of type |I s|. Meanwhile, |O| is the `output'
type in which we must interpret the whole node. I separate
inputs and outputs when specifying individual nodes, but the
connection between them will appear when we tie the recursive knot.
When we ask for substructures with |delta| branching over |B|, we must say
which sort each must take via |s : B -> S|, and then we will learn
the interpretations of those substructures before we continue.
Eventually, we must signal `end of node' with |iota| and specify the
output. As you can see, |sigma| and |delta| pack up |Set|s, so |IR|
codes are certainly large: the interpretation types |I| and |O| can
be still larger.

Now, to interpret these codes as record types, we shall need the usual
notion of dependent pair types. We shall need |Sg| for nothing larger
than |Set|, because although |IR| types can have large interpretations,
the types themselves are small.
\begin{code}
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field fst : S ; snd : T fst
open Sg
\end{code}

By way of abbreviation, let me also introduce the notion of a
sort-indexed family of maps, between sort-indexed families of sets.
\begin{code}
_-:>_ : forall {l}{S : Set}(X : S -> Set)(I : S -> Set l) -> Set l
X -:> I = forall {s} -> X s -> I s
\end{code}

If we know what the recursive substructures are and how to interpret them,
we can say what nodes consist of.
\begin{code}
<!_!>Set :  forall {l S I O}(T : IR {l} I O)  (X : S -> Set)(i : X -:> I)
                                              -> Set
<! iota oo      !>Set  X i = One
<! sigma A T    !>Set  X i = Sg A \ a -> <! T a !>Set X i
<! delta B s T  !>Set  X i = Sg ((b : B) -> X (s b)) \ r -> <! T (i o r) !>Set X i
\end{code} 
Moreover, we can read off their output.
\begin{code}
<!_!>out :  forall {l S I O}(T : IR {l} I O)  (X : S -> Set)(i : X -:> I)
                                              -> <! T !>Set X i -> O
<! iota oo      !>out  X i <>       = oo
<! sigma A T    !>out  X i (a , t)  = <! T a !>out X i t
<! delta B s T  !>out  X i (r , t)  = <! T (i o r) !>out X i t
\end{code}

Now we can tie the recursive knot. Again, I make use of Abel's sized
types to be precise about why |decode| terminates.
\begin{code}
mutual

  data Mu {l}{S}{I}(F : (s : S) -> IR {l} I (I s))(j : Size)(s : S) : Set
    where  <<_>> : {k : Size< j} -> <! F s !>Set (Mu F k) decode -> Mu F j s

  decode : forall {l}{S}{I}{F}{j} -> Mu {l}{S}{I} F j -:> I
  decode {F = F}{s = s} << n >> = <! F s !>out (Mu F _) decode n
\end{code}
Of course, you and I can see from the definition of |<!_!>out| that the
recursive uses of |decode| will occur only at substructures, but without
sized types, we should need to inline |<!_!>out| to expose that guardedness
to Agda.

Now, as Ghani and Hancock observe, |IR I| is a (relative)
monad \cite{MSC:9428192}.\footnote{They observe also that |<!_!>Set| and |<!_!>out| form a monad morphism.} Indeed,
it is the free monad generated by |sigma| and |delta|. Its |>>=|
operator is perfectly standard, concatenating dependent record types.
I omit the unremarkable proofs of the laws.
%format IRK = "\F{IRK}"
%format I>= = >>= "_{\D{I}}"
%format _I>=_ = _ I>= )
\begin{code}
IRK : forall {l}{S}{I : S -> Set l} -> Kleisli (IR I)
IRK {l}{S}{I} = record { return = iota ; _>>=_ = _I>=_ } where
  _I>=_ : forall {X Y} -> IR I X -> (X -> IR I Y) -> IR I Y
  iota x       I>= K = K x
  sigma A T    I>= K = sigma A \ a -> T a I>= K
  delta B s T  I>= K = delta B s \ f -> T f I>= K
\end{code}

%if False
\begin{code}
IRKL : forall {l}{S}{I : S -> Set l} -> KleisliLaws (IRK {l}{S}{I})
IRKL {l}{S}{I} = record
    { idLeft = \ g -> ext (idl o g)
    ; idRight = \ f -> refl
    ; assoc = \ f g h -> ext (ass f g o h)
    } where
    open Kleisli (IRK {l}{S}{I})
    .idl : {X : Set l}(T : IR I X) -> (T >>= iota) == T
    idl (iota oo) = refl
    idl (sigma A T) = <^ sigma A ^> =$= ext \ a -> idl (T a)
    idl (delta B s T) = <^ delta B s ^> =$= ext \ f -> idl (T f)
    .ass : {B C D : Set l}(f : C -> IR I D)(g : B -> IR I C) ->
          (T : IR I B) -> (T >>= (f <-< g)) == ((T >>= g) >>= f)
    ass f g (iota oo) = refl
    ass f g (sigma A T) = <^ sigma A ^> =$= ext \ a -> ass f g (T a)
    ass f g (delta B s T) = <^ delta B s ^> =$= ext \ h -> ass f g (T h)
\end{code}
%endif

Now, the Bove-Capretta method amounts to a monad morphism from
|General S T| to |IR T|. That is, the domain predicate is indexed over
|S|, with domain evidence for a given |s| |decode|d in |T s|.
We may generate the morphism as usual from the
treatment of a typical |call s|, demanding the single piece of evidence
that |s| is also in the domain, then returning at once its decoding.
%format callInDom = "\F{callInDom}"
%format DOM = "\F{DOM}"
\begin{code}
callInDom : forall {l S T} -> (s : S) -> IR {l} T (T s)
callInDom s = delta One (const s) \ t -> iota (t <>)

DOM : forall {S T} -> PiG S T -> (s : S) -> IR T (T s)
DOM f s = morph IRK callInDom (f s)
\end{code}

Now, to make a given |f : PiG S T| total, it is sufficient to show
that its domain predicate holds for all |s : S|.
%format total = "\F{total}"
\begin{code}
total : forall  {S T}(f : PiG S T)(allInDom : (s : S) -> Mu (DOM f) _ s) ->
                (s : S) -> T s
total f allInDom = decode o allInDom
\end{code}
The absence of |sigma| from |callInDom| tells us that domain evidence
contains at most zero bits of data and is thus `collapsible' in Edwin
Brady's sense~\cite{DBLP:conf/types/BradyMM03}, thus enabling |total f|
to be
compiled for run time execution exactly as the na\"i{}ve recursive
definition of |f|.


\section{Discussion}

We have seen how to separate the business of saying what it is to
\emph{be} a recursive definition from the details of what it means to
\emph{run} a recursive program. The former requires only that we work
in the appropriate free monad to give us an interface permitting the
recursive calls we need to make. Here, I have considered only
recursion at a fixed arity, but the method should readily extend to
partially applied recursive calls, given that we need only account for
their \emph{syntax} in the first instance. It does not seem like a big
stretch to expect that the familiar equational style of recursive
definition could be translated monadically, much as we see in the
work on algebraic effects.

The question, then, is not what is \emph{the} semantics for general
recursion, but rather how to make use of recursive definitions in
diverse ways by giving appropriate monad morphisms---that is, by
explaining how each individual call is to be handled. We have seen
a number of useful possibilities, not least the Bove-Capretta
domain construction, by which we can seek to establish the totality
of our function and rescue it from its monadic status.

However, the key message of this paper is that the status of general
recursive definitions is readily negotiable within a total framework.
There is no need to give up on the ability either to execute potentially
nonterminating computations or to be trustably total. There is no
difference between what you can \emph{do} with a partial language and
what you can \emph{do} with a total languge: the difference is in what
you can \emph{know}. The time for wilful ignorance is over.

\bibliographystyle{plain}
\bibliography{Totality.bib}

\end{document}

