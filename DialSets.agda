-- Adapting Eric Bond's file 
module DialSets where 

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma 
open import Data.Product
open import Data.Sum.Base using (_⊎_; inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂ ; cong-app; subst)


data Two : Set where ⊤ ⊥ : Two

postulate 
    _≤₂_ : Two → Two → Set
    
    {- So here we are recalling that in Two ⊥ ≤₂ ⊤. 
    -}
    
    _⊗²_ : Two → Two → Two
    -- here we recall the conjunction on Two
    
-- Eric mentioned he'd get a better notion for objects of DialSet

record DialSet {ℓ : Level} : Set (lsuc ℓ) where
    constructor ⟨_⇒_⇒2⟩∋_
    field
        U : Set ℓ 
        X : Set ℓ
        α : U → X → Two  

{-
    DialSet is a record. In Agda, Records also have Modules (CS module not math module)
        see https://agda.readthedocs.io/en/v2.6.2.1/language/record-types.html#record-modules for details

    So there is a module DialSet and "open"ing that module causes the definitions 'U', 'X', and 'alpha' to be in scope

    Here I have commented it out and opted to only open DialSet locally seen in the definition of DialSetMap
-}


-- variables for objects of DialSet: A, B, C
-- objects are triples A= (U, X, alpha) U, X sets, alpha:U x X -> Two a function
-- maps from A to B= (V, Y, beta) are pairs of functions (f,F) f:U -> V, F:U x Y -> X such that
-- ∀ (u : U)∀ (y : Y) (u alpha F(u,y) \leq (fu beta y)
-- using version of category using maps into Two

record DialSetMap {ℓ} (A B : DialSet {ℓ}) : Set ℓ where 
    constructor _∧_st_
    open DialSet A 
    open DialSet B renaming (U to V ; X to Y ; α to β )
    -- ^ this brings U X α of object A := (U, X, α) in scope
    -- it also bring V Y β of object B := (V, Y, β) in scope
    field 
        f : U → V
        F : U → Y → X 
        cond : (u : U)(y : Y) → α u (F u y) ≤₂ β (f u) y


infix 2 _⊗ᴰ_ 
_⊗ᴰ_ : DialSet → DialSet → DialSet
⟨ U ⇒ X ⇒2⟩∋ α ⊗ᴰ ⟨ V ⇒ Y ⇒2⟩∋ β = ⟨ U × V ⇒ (V → X) × (U → Y) ⇒2⟩∋ m

                where m : U × V → (V → X) × (U → Y) → Two
                      m (u , v) (V⇒X , U⇒Y) = α u (V⇒X v) ⊗² β v (U⇒Y u)


--  Monoidal structures on DialSet

-- tensor \ox
-- in Poly notation Ayᴮ × Cyᴰ = ACyᴮᴰ
-- Poly notation: Dirichlet tensor

{-
_⊗ᴰ_ : DialSet → DialSet → DialSet
A ⊗ᴰ B = record { U × V , X x Y , alpha x beta } 
-}


{-
--product \&
-- Ayᴮ & Cyᴰ = ACyᴮ⁺ᴰ

_&_ : DialSet → DialSet → DialSet
A & B = record { U × V ; X + Y; choose(alpha, beta) }
-- want to choose a relation for a pair ((u,v), s), where s= (x, o) or (y, 1). if s=(x, 0) choose  alpha, if (y,1) choose beta


record DialSet[_,_](A B : DialSet) : Set where
    constructor _⇒ₚ_
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir q (onPos i) → dir p i
open Dialset[_,_]


-- Chart
-- forward on positions and forward on arrows
-- https://www.youtube.com/watch?v=FU9B-H6Tb4w&list=PLhgq-BqyZ7i6IjU82EDzCqgERKjjIPlmh&index=9
-- found DJM's book! http://davidjaz.com/Papers/DynamicalBook.pdf

record Chart (p q : Poly) : Set where
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir p i → dir q (onPos i)

-- write out the commuting square 




   


-}
