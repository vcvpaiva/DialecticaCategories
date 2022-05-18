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
    maybe just write ⊥ ≤ ⊤ ?
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
        
 -- for the moment the notation means that ⟨_⇒_⇒2⟩∋_ is the schema for ⟨U⇒X⇒2⟩∋alpha     

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
-- using version of category that maps into Two

record DialSetMap {ℓ} (A B : DialSet {ℓ}) : Set ℓ where 
    constructor _∧_st_
    open DialSet A 
    open DialSet B renaming (U to V ; X to Y ; α to β )
    -- ^ this brings U X α of object A := (U, X, α) in scope
    -- it also brings V Y β of object B := (V, Y, β) in scope
    field 
        f : U → V
        F : U → Y → X 
        cond : (u : U)(y : Y) → α u (F u y) ≤₂ β (f u) y
        
        -- write only ≤, please?
        
 -- Have objects and maps of DialSet, need to define composition of maps: 
 -- [(f, F);(g, G)]:= (f;g, "comp") where scare-quoted  comp(osition) means
 -- "comp":U×Z->X given by ∀ (u : U)∀ (z : Z) first duplicate u:U to get (u : U)(u' : U)(z : Z), then apply f in middle coordinate,
 -- to get (u : U)(f(u'): V)(z : Z) then apply G:V×Z->Y to last two components, to get  (u:U, G(f(u'), z) in U, Y and finally apply F to it
 
 
 -- need to define identities 1_A= (id_U, \pi_2:U\times X-> X)
 -- need to prove composition is associative (f,F);[(g,G);(h, H)]= [(f,F);(g,G)];(h,H)
 -- and identity laws 


--  Monoidal structures on DialSet

-- 1. The useful tensor product \ox^D
-- in Poly notation Ayᴮ × Cyᴰ = ACyᴮᴰ
-- in Poly notation this is called the Dirichlet product


_⊗ᴰ_ : DialSet → DialSet → DialSet
A ⊗ᴰ B = record { U × V ; X x Y ; alpha x beta } 
 -- define alpha x beta



-- 2. The cartesian product \&
-- in Poly notation Ayᴮ & Cyᴰ = ACyᴮ⁺ᴰ

_&_ : DialSet → DialSet → DialSet
A & B = record { U × V ; X + Y; choose(alpha, beta) }
-- want to choose a relation for a pair ((u,v), s), where s= (x, o) or (y, 1). if s=(x, 0) choose  alpha, if (y,1) choose beta

-- Next the internal-hom in DialSet

record DialSet[_,_](A B : DialSet) : Set where
    constructor _⇒ₚ_
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir q (onPos i) → dir p i
open Dialset[_,_]

-- Next is a different tensor product (the crossed tensor product) that only appears in chapter 3 of thesis

infix 2 _⊗ᴮ_ 

_⊗ᴮ_ : DialSet → DialSet → DialSet

⟨ U ⇒ X ⇒2⟩∋ α ⊗ᴮ ⟨ V ⇒ Y ⇒2⟩∋ β = ⟨ U × V ⇒ (V → X) × (U → Y) ⇒2⟩∋ m

                where m : U × V → (V → X) × (U → Y) → Two
                      m (u , v) (V⇒X , U⇒Y) = α u (V⇒X v) ⊗² β v (U⇒Y u)


-- Monoids and Comonoids in DialSets


-- Chart
-- forward on positions and forward on arrows
-- https://www.youtube.com/watch?v=FU9B-H6Tb4w&list=PLhgq-BqyZ7i6IjU82EDzCqgERKjjIPlmh&index=9
-- DJM's book! http://davidjaz.com/Papers/DynamicalBook.pdf

record Chart (p q : Poly) : Set where
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir p i → dir q (onPos i)

-- write out the commuting square 




   



