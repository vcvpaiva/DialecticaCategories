-- Copying Eric Bond's file for Poly to adapt it.
module DialSets where 

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma 
open import Data.Product
open import Data.Sum.Base using (_⊎_; inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂ ; cong-app; subst)
-- need to import less or equal \leq too?

data Two : Set where ⊤ ⊥ : Two

postulate 
    _≤₂_ : Two → Two → Set
    {- So here we are postulating a relation on Two. 
    this is similar to what is done with Lineales here
    https://github.com/heades/cut-fill-agda/blob/5ae2c4bde0b7c63930cf8ab2733e3eef071672c1/DialSets.agda#L16
    -}
    _⊗²_ : Two → Two → Two
    -- here we postulate a monoidal product on Two

record DialSet {ℓ : Level} : Set (lsuc ℓ) where
    constructor _⋆_⇒2∋_
    field
        U : Set ℓ 
        X : Set ℓ
        α : U × X -> Two  

-- open DialSet
-- what this opening statement?
{-
    DialSet is a record. In Agda, Records also have Modules (Cs module not math module)
        see https://agda.readthedocs.io/en/v2.6.2.1/language/record-types.html#record-modules for details

    So there is a module DialSet and "open"ing that module causes the definitions 'U', 'X', and 'alpha' to be in scope

    Here I have commented it out and opted to only open DialSet locally seen in the definition of DialSetMap
-}


-- variables for objects of DialSet: a, b, c
-- objects are triples a= (U; X; alpha) U,X sets, alpha:U x X ->2 a function
-- maps from a to b= (V; Y; beta) are pairs of functions (f,F) f:U -> V, F:U x Y -> X such that
-- ∀ (u : U)∀ (y : Y) (u alpha F(u,y) \leq (fu beta y)

record DialSetMap {ℓ} (A B : DialSet {ℓ}) : Set ℓ where 
    constructor _∧_st_
    open DialSet A 
    open DialSet B renaming (U to V ; X to Y ; α to β )
    -- ^ this brings U X α of object A := (U, X, α) in scope
    -- it also bring V Y β of object B := (V, Y, β) in scope
    field 
        f : U → V
        F : U × Y → X 
        cond : (u : U)(y : Y) → α (u , F (u , y)) ≤₂ β (f u , y)


-- need a monoidal operation to combine elements of Two
-- similar to https://github.com/heades/cut-fill-agda/blob/5ae2c4bde0b7c63930cf8ab2733e3eef071672c1/DialSets.agda#L144
_⊗ᴰ_ : DialSet → DialSet → DialSet
(U ⋆ X ⇒2∋ α) ⊗ᴰ (V ⋆ Y ⇒2∋ β) = 
                (U × V) ⋆ 
                ((V → X) × (U → Y)) ⇒2∋ 
                λ{ ((u , v) , V⇒X , U⇒Y ) → α (u , V⇒X v) ⊗² β (v , U⇒Y u) }   

-- how do I write the above?

--  monoidal structures on DialSet
-- tensor \ox
-- Ayᴮ × Cyᴰ = ACyᴮᴰ
{-
_⊗ₚ_ : DialSet → DialSet → DialSet
a ⊗ₚ b = record { U × V ; X x Y }; alpha x beta } 




--product \&
-- Ayᴮ × Cyᴰ = ACyᴮ⁺ᴰ

_×ₚ_ : DialSet → DialSet → DialSet
a ×ₚ b = record { U × V ; X + Y; choose(alpha, beta) }
-- want to choose a relation for a pair ((u,v), s), where s= (x, o) or (y, 1). if s=(x, 0) choose  alpha, otherwise choose beta


record DialSet[_,_](a b : DialSet) : Set where
    constructor _⇒ₚ_
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir q (onPos i) → dir p i
open Dialset[_,_]

-- RENAME 
_⇒∘ₚ_ : {p q r : Poly} → Poly[ p , q ] → Poly[ q , r ] → Poly[ p , r ]
pq ⇒∘ₚ qr = record { onPos = (onPos pq) ؛ (onPos qr) -- forward composition on positions
                  ; onDir = λ i → ((onDir pq) i) o ((onDir qr) ((onPos pq) i)) } -- backward composition on directions
                  

-- Chart
-- forward on positions and forward on arrows
--https://www.youtube.com/watch?v=FU9B-H6Tb4w&list=PLhgq-BqyZ7i6IjU82EDzCqgERKjjIPlmh&index=9
-- found DJM's book! http://davidjaz.com/Papers/DynamicalBook.pdf
record Chart (p q : Poly) : Set where
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir p i → dir q (onPos i)

-- write out the commuting square 

Poly[] : Poly → Poly → Set
Poly[] p q = ∀ (i : pos p) → Σ (pos q) (λ (j : pos q) → ∀ (d : dir q j) → Σ (dir p i) λ c → Unit )


lemma-poly[]-iso : {p q : Poly} → Poly[] p q ≈ Poly[ p , q ]
lemma-poly[]-iso {p} {q} = record { to = λ p[] → record { onPos = λ ppos → fst( p[] ppos) ; onDir = λ ppos x → fst(snd(p[] ppos) x) } 
                        ; from = λ poly[p,q] ppos → (onPos poly[p,q]) ppos , λ d → (onDir poly[p,q]) ppos d , unit 
                        ; from∘to = λ poly[]pq → Extensionality λ x → {! ? !}
                        ; to∘from = λ poly[p,q] → refl }

elem : Poly → Set
elem p = Σ (pos p) (dir p)


lift : {X Y : Set} → (p : Poly) → (X → Y) → (⦅ p ⦆ X → ⦅ p ⦆ Y)
lift p f = λ{ (fst₁ , snd₁) → fst₁ , snd₁ ؛ f}

yˢ : (S : Set) → Poly
yˢ S = Unit ▹ λ _ → S

𝓎 : Poly
𝓎 = Unit ▹ (λ _ → Unit)

yoneda : {S : Set} → {q : Poly} → Poly[ yˢ S , q ] ≈ ⦅ q ⦆ S
yoneda =  record { to = λ{ record { onPos = onPos ; onDir = onDir } → onPos unit , λ x → onDir unit x } 
                    ; from = λ { (fst₁ , snd₁) → record { onPos = λ _ → fst₁ ; onDir = λ i → snd₁ } } 
                    ; from∘to = λ{ record { onPos = onPos ; onDir = onDir } → {! refl  !} } 
                    ; to∘from = λ { (fst₁ , snd₁) → refl } }


-- Day 5 (Closures)
-- Poly(p ⊗ q , r) ≈ Poly (p , [q , r])
-- Poly(p × q , r) ≈ Poly (p , qʳ)
-- where [q , r] and qʳ are not defined here yet



   


-}