{-# OPTIONS --type-in-type #-}

module Lec3 where

open import Lec1
open import Lec2

postulate 
    extensionality : {S : Set}{T : S -> Set}
                     (f g : (x : S) -> T x) ->
                     ((x : S) -> f x == g x) ->
                     f == g

record Category : Set where
    field
        -- two types of thing
        Obj  : Set -- "points" or "objects"
        _~>_ : Obj -> Obj -> Set -- "arrows" or "morphisms"

        -- two operations
        id~>  : {T : Obj} -> T ~> T
        _>~>_ : {R S T : Obj} -> R ~> S -> S ~> T -> R ~> T

        -- three laws
        law-id~>>~> : {S T : Obj} (f : S ~> T) -> (id~> >~> f) == f
        law->~>id~> : {S T : Obj} (f : S ~> T) -> (f >~> id~> ) == f
        law->~>>~> : {Q R S T : Obj} (f : Q ~> R) (g : R ~> S)(h : S ~> T) ->
                        ((f >~> g) >~> h) == (f >~> (g >~> h))