{-# OPTIONS --copatterns #-}

module Sizey where

open import Agda.Primitive
postulate
  Size : Set
  Size<_ : Size → Set
  up : Size → Size
  infinite : Size
{-# BUILTIN SIZE Size #-}
{-# BUILTIN SIZELT Size<_ #-}
{-# BUILTIN SIZESUC up #-}
{-# BUILTIN SIZEINF infinite #-}

mutual
  data Delay (i : Size)(X : Set) : Set where
    now : X -> Delay i X
    later : Delayter i X -> Delay i X
  record Delayter (i : Size)(X : Set) : Set where
    coinductive
    field force : {j : Size< i} -> Delay j X
open Delayter

mutual
    _>>=_ : forall {i A B} -> Delay i A -> (A -> Delay i B) ->
              Delay i B
    now a >>= f = f a
    later a' >>= f = later (a' >>=' f)
    _>>='_ : forall {i A B} → Delayter i A -> (A -> Delay i B)
              -> Delayter i B
    force (a' >>=' f) = force a' >>= f

module FOO (S : Set)(T : S -> Set) where

  data G (X : Set) : Set where
    !! : X -> G X
    _??_ : (s : S)(k : T s -> G X) -> G X

  morph : {i : Size}(f : (s : S) -> Delay i (T s))
          {X : Set} -> G X -> Delay i X
  morph f (!! x) = now x
  morph f (s ?? k) = f s >>= \ t -> morph f (k t)

  delay : {i : Size}(f : (s : S) -> G (T s)) ->
          {X : Set} -> G X -> Delay i X
  delayter : {i : Size}(f : (s : S) -> G (T s)) ->
          {X : Set} -> G X -> Delayter i X
  delay f = morph (\ s -> later (delayter f (f s)))
  force (delayter f g) = delay f g

