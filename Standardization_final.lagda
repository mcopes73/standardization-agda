\begin{code}
module Standardization_final where
open import Term
open import Chi
open import Substitution
open import Alpha
open import SubstitutionLemmas

open import Data.Nat.Properties
open import Data.Vec
open import Data.List
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary hiding (Rel)
open import Relation.Binary.PropositionalEquality as PropEq renaming (trans to ≡-trans)
open import Data.Product renaming (Σ to Σₓ)
open import Data.Nat as Nat hiding (_*_)

infixl 1 _⟶β_
infixl 1 _⟶hap_
infixl 1 _→→hap_
infix 1 _→→st_
infix 0 _[_:=_]
_[_:=_] : Λ -> V -> Λ -> Λ

M [ x := N ] = M ∙ (ι ≺+ (x , N))

data _∨_ (P Q : Set) : Set where
   ∨-intro₁ : P → P ∨ Q
   ∨-intro₂ : Q → P ∨ Q

data _∧_ (P Q : Set) : Set where
   ∧-intro : P → Q → P ∧ Q

∧-elim-l : ∀{P Q} -> P ∧ Q -> P
∧-elim-l (∧-intro x y) = x

∧-elim-r : ∀{P Q} -> P ∧ Q -> Q
∧-elim-r (∧-intro x y) = y

data isAbs : Λ -> Set where
  abs : forall {x M} -> isAbs (ƛ x M)

isAbs? : (M : Λ) -> Dec (isAbs M)
isAbs? (v x) = no (λ ())
isAbs? (M · N) = no (λ ())
isAbs? (ƛ x M) = yes abs

noAbsα : ∀ {A B} -> ¬ isAbs A -> B ∼α A -> ¬ isAbs B
noAbsα ¬isAbsx ∼v = ¬isAbsx
noAbsα ¬isAbsAB (∼· y y₁) = λ ()
noAbsα ¬isAbsA (∼ƛ x₂ x₃ y₁) = λ _ → ¬isAbsA abs

¬isAbsAB : ∀ {M N} -> ¬ isAbs (M · N)
¬isAbsAB = λ ()

isAbsα : ∀ {A B} -> isAbs A -> B ∼α A -> isAbs B
isAbsα isAbsx ∼v = isAbsx
isAbsα isAbsAB (∼· y y₁) = ⊥-elim (¬isAbsAB isAbsAB)
isAbsα x₁ (∼ƛ x₂ x₃ y₁) = abs

-- Counts the number of redexes in a Term
countRedexes : Λ -> ℕ
countRedexes (v _) = 0
countRedexes (M · N) with isAbs? M
... | yes _ = suc (countRedexes M + countRedexes N)
... | no _ = countRedexes M + countRedexes N
countRedexes (ƛ _ M) = countRedexes M

-- Definition 2.1 For λ-terms M, N and a natural number n ≥ 0, we define a relation M →n N inductively as follows.
-- M β N ↧ n represents that N is obtained by contracting the n-th redex in M.
data _β_↧_ : Λ -> Λ -> ℕ -> Set where
  outer-redex : ∀ {x A B} -> ((ƛ x A) · B) β (A [ x := B ]) ↧ 0
  appNoAbsL : ∀ {n A B C} -> A β B ↧ n -> ¬ isAbs A
    -> (A · C) β (B · C) ↧ n
  appAbsL : ∀ {n A B C} -> A β B ↧ n -> isAbs A
    -> (A · C) β (B · C) ↧ (suc n)
  appNoAbsR : ∀ {n A B C} -> A β B ↧ n -> ¬ isAbs C
    -> (C · A) β (C · B) ↧ (n + countRedexes C)
  appAbsR : ∀ {n A B C} -> A β B ↧ n -> isAbs C
    -> (C · A) β (C · B) ↧ (suc (n + countRedexes C))
  abs : ∀ {n x A B} -> A β B ↧ n -> (ƛ x A) β (ƛ x B) ↧ n

β-example1 : ∀{x y z} -> ((ƛ x ((ƛ y (v y)) · (v x))) · (v z)) β ((ƛ x ((v y) [ y := v x ])) · (v z)) ↧ 1
β-example1 = appAbsL (abs outer-redex) abs



data _⟶βalt_ : Λ -> Λ -> Set where
  redex : ∀ {x M N} -> ((ƛ x M) · N) ⟶βalt (M [ x := N ])
  app-l : ∀ {M M' N} -> M ⟶βalt M' -> (M · N) ⟶βalt (M' · N)
  app-r : ∀ {N N' M} -> N ⟶βalt N' -> (M · N) ⟶βalt (M · N')
  abs : ∀ {x M M'} -> M ⟶βalt M' -> (ƛ x M) ⟶βalt (ƛ x M')

-- Definition 2.2
-- Beta reduction
open import Relation Λ public
_⟶β_ : Λ -> Λ -> Set
M ⟶β N = Σₓ ℕ (\n -> M β N ↧ n)

β↓→β : ∀{M N n} -> M β N ↧ n -> M ⟶β N
β↓→β {n = n} MβNn = n ∶ MβNn
 
β↓impliesβ : ∀{M N} -> M ⟶β N -> M ⟶βalt N
β↓impliesβ (_ , outer-redex) = redex
β↓impliesβ (_ , appNoAbsL AβBn _) = app-l (β↓impliesβ (β↓→β AβBn))
β↓impliesβ (_ , appAbsL AβBn _) = app-l (β↓impliesβ (β↓→β AβBn))
β↓impliesβ (_ , appNoAbsR AβBn _) = app-r (β↓impliesβ (β↓→β AβBn))
β↓impliesβ (_ , appAbsR AβBn _) = app-r (β↓impliesβ (β↓→β AβBn))
β↓impliesβ (_ , abs AβBn) = abs (β↓impliesβ (β↓→β AβBn))

βimpliesβ↓ : ∀{M N} -> M ⟶βalt N -> M ⟶β N
βimpliesβ↓ redex = zero ∶ outer-redex
βimpliesβ↓ (app-l {M} {M'} {N} M→βM') with isAbs? M
... | yes isAbsM = β↓→β (appAbsL (proj₂ (βimpliesβ↓ M→βM')) isAbsM)
... | no ¬isAbsM = β↓→β (appNoAbsL (proj₂ (βimpliesβ↓ M→βM')) ¬isAbsM)
βimpliesβ↓ (app-r {M} {M'} {N} M→βM') with isAbs? N
... | yes isAbsN = β↓→β (appAbsR (proj₂ (βimpliesβ↓ M→βM')) isAbsN)
... | no ¬isAbsN = β↓→β (appNoAbsR (proj₂ (βimpliesβ↓ M→βM')) ¬isAbsN)
βimpliesβ↓ (abs M→βM') =  β↓→β (abs (proj₂ (βimpliesβ↓ M→βM')))

≡→α : ∀ {M N} -> M ≡ N -> M ∼α N
≡→α {M} M≡N = subst₂ _∼α_ refl M≡N (∼ρ {M})

lem-βex : ∀{A B n} -> A β B ↧ n -> A ⟶β B
lem-βex {A} {B} {n} AβBn = (n , AβBn)

lem-βappr : ∀{A B C} -> A ⟶β B -> A · C ⟶β B · C
lem-βappr (.0 ∶ outer-redex) = zero ∶ appNoAbsL outer-redex (λ ())
lem-βappr (n ∶ appNoAbsL AβBn x) = n ∶ appNoAbsL (appNoAbsL AβBn x) (λ ())
lem-βappr (n ∶ appAbsL AβBn x) = lem-βex (appNoAbsL (appAbsL AβBn x) (λ ()))
lem-βappr (n ∶ appNoAbsR AβBn x) = lem-βex (appNoAbsL (appNoAbsR AβBn x) (λ ()))
lem-βappr (n ∶ appAbsR AβBn x) = lem-βex (appNoAbsL (appAbsR AβBn x) (λ ()))
lem-βappr (n ∶ abs AβBn) = suc n ∶ appAbsL (abs AβBn) abs

lem-βappl : ∀{A B C} -> A ⟶β B -> C · A ⟶β C · B
lem-βappl {C = C} (m , AβBn) with isAbs? C
... | yes isAbsC = lem-βex (appAbsR AβBn isAbsC)
... | no ¬isAbsC = lem-βex (appNoAbsR AβBn ¬isAbsC)

freshness-subst-rest : ∀{A B x y σ} -> x # A ∙ σ -> x # B -> x #⇂ (σ ≺+ (y ∶ B) , A)
freshness-subst-rest {A} {B} {x} {y} {σ} x#Aσ x#B w w*M with y ≟ w
... | yes _ = x#B
... | no _ = (lemma#→free# x#Aσ) w w*M

freshness-subst : ∀{A B x y σ} -> x # A ∙ σ -> x # B -> x # A ∙ σ ≺+ (y ∶ B)
freshness-subst {A} {y = y} {σ = σ} x#Aσ x#B = lemmafree#→# {M = A} (freshness-subst-rest {y = y} {σ = σ} x#Aσ x#B)

lem#ι : ∀{A x} -> x # A -> x # A ∙ ι
lem#ι {A} {x} x#A = lemmafree#→# lem#ι-rest
      where lem#ι-rest : x #⇂ (ι , A)
            lem#ι-rest m m*A with x ≟ m
            ... | yes x≡m = ⊥-elim ((lemma-free→¬# m*A) (subst₂ _#_ x≡m refl x#A))
            ... | no x≢m = #v (sym≢ x≢m)

freshness-β : ∀{A B x} -> A ⟶β B -> x # A -> x # B
freshness-β {(ƛ w A) · N} {B} {x} (.0 ∶ outer-redex) (#· #ƛ≡ w#N) = w#Aw,N {A}
            where lemw#A : ∀{w x y σ A} -> w # (A ∙ σ) -> w ≢ y -> w # (A ∙ σ ≺+ (x ∶ (v y)))
                  lemw#A {w} {x} {y} {σ} {A} w#Aσ w≢y = freshness-subst {A} {v y} {w} {x} w#Aσ (#v (sym≢ w≢y))
                  w#w,N-rest : ∀{A} -> w #⇂ (ι ≺+ (w ∶ N) , A)
                  w#w,N-rest m m*A with w ≟ m
                  ... | yes _ = w#N
                  ... | no w≢m = #v (sym≢ w≢m)
                  w#Aw,N : ∀{A} -> w # A ∙ ι ≺+ (w ∶ N)
                  w#Aw,N {A} = lemmafree#→# {w} {ι ≺+ (w ∶ N)} {A} w#w,N-rest
freshness-β {(ƛ w A) · N} {B} {y} (.0 ∶ outer-redex) (#· (#ƛ y#A) w#N) = freshness-subst {A} {y = w} (lem#ι y#A) w#N
freshness-β (_ ∶ appNoAbsL {n} A⟶Bn _) (#· x#C x#A) =  (#· (freshness-β (n , A⟶Bn) x#C) x#A)
freshness-β (_ ∶ appAbsL {n} A⟶Bn _) (#· x#C x#A) =  (#· (freshness-β (n , A⟶Bn) x#C) x#A)
freshness-β (_ ∶ appNoAbsR {n} A⟶Bn _) (#· x#C x#A) =  (#· x#C (freshness-β (n , A⟶Bn) x#A)) 
freshness-β (_ ∶ appAbsR {n} A⟶Bn _) (#· x#C x#A) = (#· x#C (freshness-β (n , A⟶Bn) x#A)) 
freshness-β {A} {B} {x} (n ∶ abs {x = y} A⟶Bn) (#ƛ x#A) = #ƛ (freshness-β (n , A⟶Bn) x#A)  
freshness-β {A} {B} {x} (n ∶ abs {x = y} A⟶Bn) #ƛ≡ = #ƛ≡

free-β : ∀{A B x} -> A ⟶β B -> x * B -> x * A
free-β {A} {B} {x} A⟶βB x*B with x #? A
... | yes x#A = ⊥-elim ((lemma-free→¬# x*B) (freshness-β A⟶βB x#A))
... | no ¬x#A = lemma¬#→free ¬x#A

lem-βsubst : ∀{M N σ} -> M ⟶β N -> Σₓ Λ (λ N' -> (M ∙ σ ⟶β N') ∧ (N' ∼α N ∙ σ))
lem-βsubst {σ = σ} (.0 ∶ outer-redex {x} {A} {B}) = (((A ∙ (σ  ≺+ (x , (v y)))) [ y := B ∙ σ ]) , ∧-intro (0 , outer-redex) (subst₂ _∼α_ refl (corollary1Prop7 {A} {B} {x = x}) Aσ'Bσ))
                where y = χ (σ , ƛ x A)
                      Aσ'Bσ = corollary1SubstLemma {x}{χ (σ , ƛ x A)}{M = A}{N = B ∙ σ} (χ-lemma2 σ (ƛ x A))
lem-βsubst {σ = σ} (m ∶ appNoAbsL {C = C} AβBn _) with lem-βsubst {σ = σ} (m , AβBn)
... | (N' , Aσ→N'∧N'~Bσ) = (N' · (C ∙ σ) , ∧-intro (lem-βappr (∧-elim-l Aσ→N'∧N'~Bσ)) (∼· (∧-elim-r Aσ→N'∧N'~Bσ) ∼ρ))
lem-βsubst {σ = σ} (m ∶ appAbsL {C = C} AβBn _) with lem-βsubst {σ = σ} (lem-βex AβBn)
... | (N' , Aσ→N'∧N'~Bσ) = (N' · (C ∙ σ) , ∧-intro (lem-βappr (∧-elim-l Aσ→N'∧N'~Bσ)) (∼· (∧-elim-r Aσ→N'∧N'~Bσ) ∼ρ))
lem-βsubst {σ = σ} (_ ∶ appNoAbsR {C = C} AβBn _) with lem-βsubst {σ = σ} (lem-βex AβBn)
... | (N' , Aσ→N'∧N'~Bσ) = ((C ∙ σ) · N' , ∧-intro (lem-βappl (∧-elim-l Aσ→N'∧N'~Bσ)) (∼· ∼ρ (∧-elim-r Aσ→N'∧N'~Bσ)))
lem-βsubst {σ = σ} (_ ∶ appAbsR {C = C} AβBn _) with lem-βsubst {σ = σ} (lem-βex AβBn)
... | (N' , Aσ→N'∧N'~Bσ) = ((C ∙ σ) · N' , ∧-intro (lem-βappl (∧-elim-l Aσ→N'∧N'~Bσ)) (∼· ∼ρ (∧-elim-r Aσ→N'∧N'~Bσ)))
lem-βsubst {σ = σ} (m ∶ abs {x = x} {A = A} {B = B} AβBn) with lem-βsubst {σ = σ ≺+ (x , (v y))} (lem-βex AβBn)
   where y = χ (σ , ƛ x A)
... | (N' , Aσ→N'∧N'~Bσ) = (ƛ y N' , ∧-intro (lem-βex (abs (proj₂ (∧-elim-l Aσ→N'∧N'~Bσ)))) (∼τ (lemma∼λ (∧-elim-r Aσ→N'∧N'~Bσ)) (∼σ (corollary4-2 {x = x} {M = B} {σ = σ} y#σλxB))))
   where y = χ (σ , ƛ x A)
         σ' = σ ≺+ (x , (v y))
         y#⇂σ,A : y #⇂ (σ , ƛ x A)
         y#⇂σ,A = χ-lemma2 σ (ƛ x A)
         y#σλxB : y #⇂ (σ , ƛ x B)
         y#σλxB w (*ƛ w*B w!=x) = y#⇂σ,A w (*ƛ (free-β (lem-βex AβBn) w*B) w!=x)

lem-βα : ∀{M N M'} -> M ⟶β N -> M ∼α M' -> Σₓ Λ  (λ N' -> (M' ⟶β N') ∧ (N' ∼α N))
lem-βα {M} {N} {M'} (.0 ∶ outer-redex) (∼· {N = B} {N' = B'} (∼ƛ {A} {A'} {x} {z} {w} w#λxA w#λzA' A∼A') B∼B')
                                                  = ( (A' [ z := B' ]) , ∧-intro (0 , outer-redex) (∼τ A'z,B'αAxB ∼ρ))
       where Ax,B~A'z,B : (A [ x := B ]) ∼α (A' [ z := B ])
             Ax,B~A'z,B = subst₂ _∼α_ (sym (lemma≺+ w#λxA)) (sym (lemma≺+ w#λzA')) (≡→α (lemmaM∼M'→Mσ≡M'σ {σ = (ι ≺+ (w , B))} A∼A'))
             z,B'~z,B : (ι ≺+ (z , B')) ∼ασ (ι ≺+ (z , B))
             z,B'~z,B y with z ≟ y
             ... | yes  _ = (∼σ B∼B')
             ... | no   _ = ∼ρ
             A'z,B'αAxB : (A' [ z := B' ]) ∼α (A [ x := B ])
             A'z,B'αAxB = ∼τ (lemma-subst {M = A'} ∼ρ (lemma∼ασ  z,B'~z,B)) (∼σ Ax,B~A'z,B)
lem-βα (n ∶ appNoAbsL {.n} {M} {N} {C} M⟶Nn ¬isAbsM) (∼· {N' = C'} M∼M' C∼C') with lem-βα (n , M⟶Nn) M∼M'
... | ( N' , β∧∼) = (N' · C' , ∧-intro (proj₁ (∧-elim-l β∧∼) , appNoAbsL (proj₂ (∧-elim-l β∧∼)) (noAbsα ¬isAbsM (∼σ M∼M'))) (∼· (∧-elim-r β∧∼) (∼σ C∼C')))
lem-βα (n ∶ appAbsL {m} {M} {N} {C} M⟶Nn isAbsM) (∼· {N' = C'} M∼M' C∼C') with lem-βα (m , M⟶Nn) M∼M'
... | ( N' , β∧∼) = (N' · C' , ∧-intro (suc (proj₁ (∧-elim-l β∧∼)) , appAbsL (proj₂ (∧-elim-l β∧∼)) (isAbsα isAbsM (∼σ M∼M'))) (∼· (∧-elim-r β∧∼) (∼σ C∼C')))
lem-βα (n ∶ appNoAbsR {m} {M} {N} {C} M⟶Nn ¬isAbsM) (∼· {M' = C'} C∼C' M∼M') with lem-βα (m , M⟶Nn) M∼M'
... | ( N' , β∧∼) = (C' · N' , ∧-intro (proj₁ (∧-elim-l β∧∼) + countRedexes C' , appNoAbsR (proj₂ (∧-elim-l β∧∼)) (noAbsα ¬isAbsM (∼σ C∼C'))) (∼· (∼σ C∼C') (∧-elim-r β∧∼)))
lem-βα (_ ∶ appAbsR {m} {M} {N} {C} M⟶Nn isAbsM) (∼· {M' = C'} C∼C' M∼M') with lem-βα (m , M⟶Nn) M∼M'
... | ( N' , β∧∼) = (C' · N' , ∧-intro (suc ((proj₁ (∧-elim-l β∧∼) + countRedexes C')) , appAbsR (proj₂ (∧-elim-l β∧∼)) (isAbsα isAbsM (∼σ C∼C'))) (∼· (∼σ C∼C') (∧-elim-r β∧∼)))
lem-βα (n ∶ abs {.n} {x} {A} {B} A⟶Bn) (∼ƛ {.A} {A'} {.x} {x'} {y} y#λxA y#λx'A' Ax,y~A'x'y) = λx'A'⟶βλxB
       where A'~Ax,x' : (A [ x := v x' ]) ∼α A'
             A'~Ax,x' = subst₂ _∼α_ (sym (lemma≺+ y#λxA)) refl (∼τ (∼τ (≡→α (lemmaM∼M'→Mσ≡M'σ {σ = (ι ≺+ (y , v x'))} Ax,y~A'x'y)) (≡→α (lemma≺+ι y#λx'A'))) (∼σ lemma∙ι))
             Ax,x'⟶βBx,x' : Σₓ Λ (\K -> ((A [ x := v x' ]) ⟶β K) ∧ (K ∼α (B [ x := (v x')]))) 
             Ax,x'⟶βBx,x' = lem-βsubst (n , A⟶Bn)
             lemα : ∀{A B B'} -> Σₓ Λ (\K -> (A ⟶β K) ∧ (K ∼α B)) -> B ∼α B' -> Σₓ Λ (\K -> (A ⟶β K) ∧ (K ∼α B'))
             lemα (K , AK∧K~B) B~B' = (K , ∧-intro (∧-elim-l AK∧K~B) (∼τ (∧-elim-r AK∧K~B) B~B'))
             A'⟶βBx,x' : Σₓ Λ (\K -> ((A' ⟶β K) ∧ (K ∼α (B [ x := (v x')]))))
             A'⟶βBx,x' = lemα (lem-βα (∧-elim-l (proj₂ Ax,x'⟶βBx,x')) A'~Ax,x') (∧-elim-r (proj₂ Ax,x'⟶βBx,x'))
             AβK→λxAβλxK : ∀ {A B x} -> A ⟶β B -> ƛ x A ⟶β ƛ x B
             AβK→λxAβλxK (n , A⟶Bn )= (n , abs A⟶Bn)
             λx'A'⟶βλx'Bx,x' : Σₓ Λ (\K -> ((ƛ x' A' ⟶β K) ∧ (K ∼α (ƛ x' (B [ x := (v x')])))))
             λx'A'⟶βλx'Bx,x' = (ƛ x' (proj₁ A'⟶βBx,x') , ∧-intro (AβK→λxAβλxK (∧-elim-l (proj₂ A'⟶βBx,x'))) (lemma∼λ (∧-elim-r (proj₂ A'⟶βBx,x'))))
             λx'Bx,x'~λxB : ƛ x' (B [ x := (v x')]) ∼α ƛ x B
             λx'Bx,x'~λxB = ∼σ (corollary4-2' (freshness-β (n , abs A⟶Bn) (lemmaM∼N# (∼σ (∼ƛ y#λxA y#λx'A' Ax,y~A'x'y)) x' #ƛ≡)))
             λx'A'⟶βλxB : Σₓ Λ (\K -> ((ƛ x' A' ⟶β K) ∧ (K ∼α ƛ x B)))
             λx'A'⟶βλxB = lemα λx'A'⟶βλx'Bx,x' λx'Bx,x'~λxB

data α-star (⟿ : Λ -> Λ -> Set) : Λ -> Λ -> Set where
    refl : ∀{M} → α-star ⟿ M M
    α-step : ∀{M N N'} → α-star ⟿ M N' → N' ∼α N → α-star ⟿ M N
    append : ∀ {M N K} → α-star ⟿ M K → ⟿ K N → α-star ⟿ M N

α-star-singl : ∀{⟿ M N} -> ⟿ M N -> α-star ⟿ M N 
α-star-singl = append refl

α-star-trans : ∀{⟿ M N K} -> α-star ⟿ M K -> α-star ⟿ K N -> α-star ⟿ M N
α-star-trans M→→K refl = M→→K
α-star-trans M→→K (α-step K→→N' N'~N) = α-step (α-star-trans M→→K K→→N') N'~N
α-star-trans M→→K (append K→→N' N'→N) = append (α-star-trans M→→K K→→N') N'→N


-- Leftmost reduction
_⟶l_ : Λ -> Λ -> Set
M ⟶l N =  M β N ↧ 0

_→→l_ : Λ -> Λ -> Set
_→→l_ = α-star _⟶l_

_→→β_ : Λ -> Λ -> Set
_→→β_ = α-star _⟶β_

-- Standard sequence from M to N with lower bound n
data seqβ-st (M : Λ) : (N : Λ) -> ℕ -> Set where
  single : seqβ-st M M 0
  α-step : ∀ {n K N} -> seqβ-st M K n -> K ∼α N -> seqβ-st M N n
  β-step : ∀ {K n n₀ N} -> seqβ-st M K n -> K β N ↧ n₀ -> n₀ ≥ n -> seqβ-st M N n₀

-- Head reduction in application
data _⟶hap_ : Λ -> Λ -> Set where
  hap-head : ∀{x A B} -> (ƛ x A) · B ⟶hap (A [ x := B ])
  hap-chain : ∀{C A B} -> A ⟶hap B -> (A · C) ⟶hap (B · C)

_→→hap_ : Λ -> Λ -> Set
_→→hap_ = α-star _⟶hap_

-- Def 3.2 (st.)
data _→→st_ (L : Λ) : Λ -> Set where
  st-var : ∀{x} -> L →→hap (v x) -> L →→st (v x)
  st-app : ∀{A B C D} -> L →→hap (A · B) -> A →→st C -> B →→st D ->
    L →→st (C · D)
  st-abs : ∀{x A B} -> L →→hap (ƛ x A) -> A →→st B -> L →→st (ƛ x B)
  st-alpha : ∀{A' A} -> L →→st A' -> A' ∼α A -> L →→st A

-- Lemma 3.3
-- (1)
lem-hap¬Abs : ∀{M N} -> M ⟶hap N -> ¬ isAbs M 
lem-hap¬Abs hap-head  ()
lem-hap¬Abs (hap-chain x) ()

lem-l-app : ∀ {M N C} -> M ⟶l N -> ¬ isAbs M -> (M · C) ⟶l (N · C)
lem-l-app M⟶N↧0 ¬isAbsM = appNoAbsL M⟶N↧0 ¬isAbsM

lem-hap→l : ∀ {M N} -> M ⟶hap N -> M ⟶l N
lem-hap→l hap-head = outer-redex
lem-hap→l (hap-chain A→hapB) with lem-hap→l A→hapB
... | A⟶B↧0 = appNoAbsL A⟶B↧0 (lem-hap¬Abs A→hapB)

hap→l : ∀{M N} -> M →→hap N -> M →→l N
hap→l refl = refl
hap→l (α-step M→→hapK K~N) = α-step (hap→l M→→hapK) K~N
hap→l (append M→→hapK K⟶hapN) = append (hap→l M→→hapK) (lem-hap→l K⟶hapN)

-- (2)
append-seq0 : ∀ {M N K n} -> seqβ-st M N 0 -> seqβ-st N K n -> seqβ-st M K n
append-seq0 {n = n} seqMNn single = seqMNn
append-seq0 seqMNn (α-step seqNHn' H∼αK) = α-step (append-seq0 seqMNn seqNHn') H∼αK
append-seq0 seqMNn (β-step seqNHm H→K↓n n≥m) = β-step (append-seq0 seqMNn seqNHm) H→K↓n n≥m

abs-seq : ∀ {x M N n} -> seqβ-st M N n -> seqβ-st (ƛ x M) (ƛ x N) n
abs-seq single = single
abs-seq {x} {M} {N} (α-step {K = K} seqMKn K∼αN) = α-step seqλMλKn (∼ƛ #ƛ≡ #ƛ≡ (≡→α (lemmaM∼M'→Mσ≡M'σ K∼αN)))
                       where seqλMλKn = abs-seq seqMKn
abs-seq {x} (β-step seqMKn K→N↓m n≤m) = β-step (abs-seq {x} seqMKn) (abs K→N↓m) n≤m 

lem+≡ : ∀ {x y z w} -> x ≡ y -> z ≡ w -> x + z ≡ y + w
lem+≡ refl refl = refl

absι→ : ∀{A} -> isAbs A -> isAbs (A ∙ ι)
absι→ {v x} isAbsA = isAbsA
absι→ {A · A₁} () 
absι→ {ƛ x A} isAbsA = abs

absι← : ∀{A} -> isAbs (A ∙ ι) -> isAbs A
absι← {v x} isAbsA = isAbsA
absι← {A · A₁} () 
absι← {ƛ x A} isAbsA = abs

-- A substitution where each variable is only changed for another variable.
onlyVars : Σ -> Set
onlyVars σ = (x : V) → Σₓ V (λ y -> σ x ≡ v y)

ιonlyVars : onlyVars ι
ιonlyVars = λ x → x ∶ refl

onlyVars-append : ∀{σ x y} -> onlyVars σ -> onlyVars (σ ≺+ (x , v y))
onlyVars-append {σ} {x}{y} onlyVarsσ x' with x ≟ x'
... | yes x≡x' = y ∶ refl
... | no  x≠x' = onlyVarsσ x'

onlyVars-¬isAbs : ∀{M σ} -> onlyVars σ -> ¬ (isAbs M) -> ¬ (isAbs (M ∙ σ))
onlyVars-¬isAbs {v x} {σ} onlyVarsσ ¬isAbsM with onlyVarsσ x 
... | ( y , σx≡v ) = (λ isAbsσx -> (⊥-elim (¬isAbsy (subst isAbs σx≡v isAbsσx))))
                   where ¬isAbsy : ¬ (isAbs (v y))
                         ¬isAbsy ()
onlyVars-¬isAbs {M · M₁} {σ} onlyVarsσ ¬isAbsM = λ ()
onlyVars-¬isAbs {ƛ x M} {σ} onlyVarsσ ¬isAbsM = λ _ → ¬isAbsM abs 

onlyVars-isAbs : ∀{M σ} -> onlyVars σ -> isAbs M -> isAbs (M ∙ σ)
onlyVars-isAbs {v x} {σ} onlyVarsσ isAbsM with onlyVarsσ x 
... | ( y , σx≡v ) = ⊥-elim (¬isAbsx isAbsM)
                 where ¬isAbsx : ¬ (isAbs (v x))
                       ¬isAbsx ()
onlyVars-isAbs {M · M₁} {σ} onlyVarsσ isAbsM = ⊥-elim (¬isAbsM isAbsM)
                 where ¬isAbsM : ¬ (isAbs (M · M₁))
                       ¬isAbsM ()
onlyVars-isAbs {ƛ x M} {σ} onlyVarsσ isAbsM = abs 

-- A substitution maping only vars has no effect in the count of redexes
lem-λredexCount : ∀{M σ} -> onlyVars σ -> countRedexes (M ∙ σ) ≡ countRedexes M
lem-λredexCount {v x}{σ} onlyVarsσ with onlyVarsσ x 
... | ( _ , σx≡v ) = cong countRedexes σx≡v
lem-λredexCount {M · M'}{σ} onlyVarsσ with isAbs? (M ∙ σ) | isAbs? M
... | yes isAbsM | yes isAbsM' = cong suc (lem+≡ (lem-λredexCount {M} onlyVarsσ) (lem-λredexCount {M'} onlyVarsσ))
... | yes isAbsM | no ¬isAbsM' = ⊥-elim ((onlyVars-¬isAbs onlyVarsσ ¬isAbsM') isAbsM)
... | no ¬isAbsM | yes isAbsM' = ⊥-elim (¬isAbsM (onlyVars-isAbs onlyVarsσ isAbsM'))
... | no ¬isAbsM | no ¬isAbsM' = lem+≡ (lem-λredexCount {M} onlyVarsσ) (lem-λredexCount {M'} onlyVarsσ)
lem-λredexCount {ƛ x₁ M}{σ} onlyVarsσ = lem-λredexCount {M} (onlyVars-append {σ} {x₁} onlyVarsσ)

α→sameRedexCount : ∀ {A B} -> A ∼α B -> countRedexes A ≡ countRedexes B
α→sameRedexCount ∼v = refl
α→sameRedexCount (∼· {A} {A'} {B} {B'} A'αA B'αB) with isAbs? A' | isAbs? A
... | yes isAbsA' | yes isAbsA = cong suc (lem+≡ (α→sameRedexCount A'αA) (α→sameRedexCount B'αB))
... | yes isAbsA' | no ¬isAbsA = ⊥-elim (¬isAbsA (isAbsα isAbsA' A'αA))
... | no ¬isAbsA' | yes isAbsA = ⊥-elim (¬isAbsA' (isAbsα isAbsA (∼σ (A'αA))))
... | no ¬isAbsA' | no ¬isAbsA = lem+≡ (α→sameRedexCount A'αA) (α→sameRedexCount B'αB)
α→sameRedexCount (∼ƛ {A} {B} {x} {x'} {y} _ _ A∼αB) = subst₂ _≡_ (lem-λredexCount {A} (onlyVars-append {x = x} ιonlyVars)) (lem-λredexCount {B} (onlyVars-append {x = x'} ιonlyVars)) IH
                 where IH = α→sameRedexCount A∼αB
                       
β-abs : ∀ {A B n} -> A β B ↧ n -> ¬ (isAbs B) -> ¬ (isAbs A)
β-abs outer-redex ¬isAbsB = λ ()
β-abs (appNoAbsL x x₁) ¬isAbsB = λ ()
β-abs (appAbsL x x₁) ¬isAbsB = λ ()
β-abs (appNoAbsR x x₁) ¬isAbsB = λ ()
β-abs (appAbsR x x₁) ¬isAbsB = λ ()
β-abs (abs x₁) ¬isAbsB = λ _ → ¬isAbsB abs

≤-trans : ∀{m n k} -> m ≤ n -> n ≤ k -> m ≤ k
≤-trans z≤n y = z≤n
≤-trans (s≤s x) (s≤s y) = s≤s (≤-trans x y)

≤-refl : ∀{x} -> x ≤ x
≤-refl = ≤′⇒≤ ≤′-refl


≤-sum-r : ∀ {x y z} -> x ≤ y -> x ≤ y + z
≤-sum-r z≤n = z≤n
≤-sum-r (s≤s x) = s≤s (≤-sum-r x)

≤-sum-l : ∀ {x y z} -> x ≤ y -> x ≤ z + y
≤-sum-l {x} {y} {z} x≤y = subst₂ _≤_ refl (+-comm y z) (≤-sum-r {z = z} x≤y) 

≤-suc : ∀{x y} -> x ≤ y -> x ≤ suc y
≤-suc z≤n = z≤n
≤-suc (s≤s x≤y) = s≤s (≤-suc x≤y)

lem-≤-both : ∀{a b c} -> a ≤ b -> a + c ≤ b + c
lem-≤-both {b = b} z≤n = ≤-sum-l {z = b} ≤-refl
lem-≤-both (s≤s x) = s≤s (lem-≤-both x)

β-countRedexesR : ∀ {M N n} -> M β N ↧ n -> n ≤ countRedexes N
β-countRedexesR outer-redex = z≤n
β-countRedexesR (appNoAbsL {n} {A} {B} A⟶Bn ¬isAbsA) with isAbs? B
... | yes _ = ≤-suc (≤-sum-r (β-countRedexesR A⟶Bn))
... | no _ = ≤-sum-r (β-countRedexesR A⟶Bn)
β-countRedexesR (appAbsL {n} {A} {B} A⟶Bn isAbsA) with isAbs? B
... | yes _ = s≤s (≤-sum-r (β-countRedexesR A⟶Bn))
... | no ¬isAbsB = ⊥-elim ((β-abs A⟶Bn ¬isAbsB) isAbsA)
β-countRedexesR (appNoAbsR {n} {A} {B} {C} A⟶Bn ¬isAbsA) with isAbs? C
... | yes _ = ≤-suc (subst₂ _≤_ refl (+-comm (countRedexes B) (countRedexes C)) (lem-≤-both {c = countRedexes C} (β-countRedexesR A⟶Bn)))
... | no _ = subst₂ _≤_ refl (+-comm (countRedexes B) (countRedexes C)) (lem-≤-both {c = countRedexes C} (β-countRedexesR A⟶Bn))
β-countRedexesR (appAbsR {n} {A} {B} {C} A⟶Bn isAbsC) with isAbs? C
... | yes _ = s≤s (subst₂ _≤_ refl (+-comm (countRedexes B) (countRedexes C)) (lem-≤-both {c = countRedexes C} (β-countRedexesR A⟶Bn)))
... | no ¬isAbsC = ⊥-elim (¬isAbsC isAbsC)
β-countRedexesR (abs x₁) = β-countRedexesR x₁

≤-sum : ∀{x y z} -> y ≤ z -> y + x ≤ z + x
≤-sum {x = zero} z≤n = z≤n
≤-sum {x = (suc m)} {z = z} z≤n = ≤-sum-l {z = z} ≤-refl
≤-sum (s≤s x₁) = s≤s (≤-sum x₁)

αapp→≡ : ∀{M N M' N'} -> M · N ∼α M' · N' -> (M ∼α M') ∧ (N ∼α N')
αapp→≡ (∼· M∼M' N∼N') = ∧-intro M∼M' N∼N' 

α-sides : ∀{M N M' N'} -> M ∼α N -> M ∼α M' -> N ∼α N' -> M' ∼α N'
α-sides MαN MαM' NαN' = ∼τ (∼τ (∼σ MαM') (MαN)) NαN'

_≡α_ : ∀ A B -> Dec (A ∼α B)
v x ≡α v x₁ with x ≟ x₁
... | yes x≡x₁ = yes (subst₂ _∼α_ refl (cong v x≡x₁) (∼v {x}))
... | no  x≠x₁ = no (λ x∼x₁ -> x≠x₁ (αv→≡ x∼x₁))
          where αv→≡ : ∀{x y} -> v x ∼α v y -> x ≡ y
                αv→≡ ∼v = refl
v x ≡α (y · y₁) = no (λ ())
v x ≡α ƛ x₁ y = no (λ ())
(M · N) ≡α v x = no (λ ())
(M · N) ≡α (M' · N') with M ≡α M' | N ≡α N'
... | yes M∼M' | yes N∼N' = yes (∼· M∼M' N∼N')
... | yes M∼M' | no ¬N∼N' = no (λ MN∼M'N' -> (¬N∼N' (∧-elim-r (αapp→≡ MN∼M'N'))))
... | no ¬M∼M' | yes N∼N' = no (λ MN∼M'N' -> (¬M∼M' (∧-elim-l (αapp→≡ MN∼M'N'))))
... | no ¬M∼M' | no ¬N∼N' = no (λ MN∼M'N' -> (¬N∼N' (∧-elim-r (αapp→≡ MN∼M'N'))))
(M · N) ≡α ƛ x A = no (λ ())
ƛ x M ≡α v y = no (λ ())
ƛ x M ≡α (M' · N') = no (λ ())
ƛ x M ≡α ƛ y M' with M ≡α (M' ∙ (ι ≺+ (y , v x))) | x #? ƛ y M'
... | yes M∼M'yx | yes x#λyM'  = yes (∼ƛ #ƛ≡ x#λyM' (∼τ (subst₂ _∼α_ (sym (lemmaMι≺+x,x {x} {M})) refl (∼σ lemma∙ι)) M∼M'yx))
... | yes M∼M'yx | no ¬x#λyM'  = no (λ M∼M' -> ⊥-elim (¬x#λyM' (lemmaM∼N# M∼M' x #ƛ≡)))
... | no ¬M∼M'yx | yes x#λyM' = no (λ { (∼ƛ {y = z} z#λxM z#λyM' Mxz∼M'xz)  -> ⊥-elim (¬M∼M'yx (α-sides (≡→α (lemmaM∼M'→Mσ≡M'σ {σ = ι ≺+ (z , v x)} Mxz∼M'xz)) (∼τ (≡→α (lemma≺+ι z#λxM)) (∼σ lemma∙ι)) (≡→α (sym (lemma≺+ z#λyM')))))})
... | no ¬M∼M'yx | no ¬x#λyM' = no (λ M∼M' -> ⊥-elim (¬x#λyM' (lemmaM∼N# M∼M' x #ƛ≡)))

seq-redexCount : ∀ {A B n} -> seqβ-st A B n -> n ≤ countRedexes B
seq-redexCount single = z≤n
seq-redexCount (α-step seqAKn K∼αB) = subst₂ _≤_ refl (α→sameRedexCount K∼αB) (seq-redexCount seqAKn)
seq-redexCount (β-step seqAKn K→B↓m n≤m) = β-countRedexesR K→B↓m

lem-seq-appACBC : ∀ {A C B n} -> seqβ-st A B n -> ¬ (isAbs B) -> seqβ-st (A · C) (B · C) n
lem-seq-appACBC single ¬isAbsB = single
lem-seq-appACBC (α-step seqAK K∼αB) ¬isAbsB = α-step (lem-seq-appACBC seqAK (noAbsα ¬isAbsB K∼αB)) (∼· K∼αB ∼ρ)
lem-seq-appACBC (β-step seqAKm K→B↓n m≤n) ¬isAbsB = β-step (lem-seq-appACBC seqAKm (β-abs K→B↓n ¬isAbsB)) (appNoAbsL K→B↓n (β-abs K→B↓n ¬isAbsB)) m≤n

lem-seq-appACBC-abs : ∀ {A C B n} -> seqβ-st A B n -> isAbs B
  -> (seqβ-st (A · C) (B · C) n) ∨ (seqβ-st (A · C) (B · C) (suc n))
lem-seq-appACBC-abs single _ = ∨-intro₁ single
lem-seq-appACBC-abs (α-step seqAK K∼αB) isAbsB with (lem-seq-appACBC-abs seqAK (isAbsα isAbsB K∼αB))
... | ∨-intro₁ seqACKCn    = ∨-intro₁ (α-step seqACKCn (∼· K∼αB ∼ρ))
... | ∨-intro₂ seqACKCsucn = ∨-intro₂ (α-step seqACKCsucn (∼· K∼αB ∼ρ))
lem-seq-appACBC-abs {C = C} (β-step {K = K} seqAKm K→B↓n m≤n) isAbsB with isAbs? K
... | yes isAbsK with lem-seq-appACBC-abs {C = C} seqAKm isAbsK
...    | ∨-intro₁ seqACKCm = ∨-intro₂ (β-step seqACKCm (appAbsL K→B↓n isAbsK) (≤-step m≤n))
...    | ∨-intro₂ seqACKCsucm = ∨-intro₂ (β-step seqACKCsucm (appAbsL K→B↓n isAbsK) (s≤s m≤n))
lem-seq-appACBC-abs {C = C} (β-step {K = K} seqAKm K→B↓n m≤n) isAbsB | no ¬isAbsK
                    = ∨-intro₁ (β-step seqACKCm (appNoAbsL K→B↓n ¬isAbsK) m≤n)
                            where seqACKCm = lem-seq-appACBC {C = C} seqAKm ¬isAbsK

lem-seq-appCACB : ∀ {A C B n} -> seqβ-st A B n -> ¬ (isAbs C) -> ¬ (A ∼α B) -> seqβ-st (C · A) (C · B) (n + countRedexes C)
lem-seq-appCACB single _ ¬AαA = ⊥-elim (¬AαA ∼ρ)
lem-seq-appCACB {A} (α-step {n = n} {K = K} seqAKn K∼αB) ¬isAbsC ¬AαB with A ≡α K
... | yes A∼αK = ⊥-elim (¬AαB (∼τ A∼αK K∼αB))
... | no ¬A∼αK = α-step (lem-seq-appCACB seqAKn ¬isAbsC ¬A∼αK) (∼· ∼ρ K∼αB)
lem-seq-appCACB {A} {C} (β-step {K = K} seqAKn K→B↓m n≤m) ¬isAbsC ¬AαB with A ≡α K
... | yes A∼αK = β-step seqCACK (appNoAbsR K→B↓m ¬isAbsC) z≤n
          where seqCACK = α-step single (∼· (∼ρ {C}) A∼αK)
... | no ¬A∼αK = β-step (lem-seq-appCACB seqAKn ¬isAbsC ¬A∼αK) (appNoAbsR K→B↓m ¬isAbsC) (≤-sum n≤m)


lem-seq-appCACB-abs : ∀ {A C B n} -> seqβ-st A B n -> isAbs C -> ¬ (A ∼α B) -> seqβ-st (C · A) (C · B) (suc (n + countRedexes C))
lem-seq-appCACB-abs single _  ¬AαA = ⊥-elim (¬AαA ∼ρ)
lem-seq-appCACB-abs {A} (α-step {n = n} {K = K} seqAKn K∼αB) isAbsC ¬AαB with A ≡α K
... | yes A∼αK = ⊥-elim (¬AαB (∼τ A∼αK K∼αB))
... | no ¬A∼αK = α-step (lem-seq-appCACB-abs seqAKn isAbsC ¬A∼αK) (∼· ∼ρ K∼αB)
lem-seq-appCACB-abs {A} {C} (β-step {K = K} seqAKn K→B↓m n≤m) isAbsC ¬AαB with A ≡α K
... | yes A∼αK = β-step seqCACK (appAbsR K→B↓m isAbsC) z≤n
          where seqCACK = α-step single (∼· (∼ρ {C}) A∼αK)
... | no ¬A∼αK = β-step (lem-seq-appCACB-abs seqAKn isAbsC ¬A∼αK) (appAbsR K→B↓m isAbsC) (s≤s (≤-sum n≤m))

lem-seq-app-¬α : ∀{A B C D n m} -> seqβ-st A B n -> seqβ-st C D m -> ¬ (isAbs B) -> ¬ (C ∼α D)
                                                           -> seqβ-st (A · C) (B · D) (m + countRedexes B)
lem-seq-app-¬α seqABn single ¬isAbsB ¬C∼αD = ⊥-elim (¬C∼αD ∼ρ)
lem-seq-app-¬α {C = C} seqABn (α-step {K = K} seqCKm K∼αD) ¬isAbsB ¬C∼αD with C ≡α K
... | yes C∼αK = ⊥-elim (¬C∼αD (∼τ C∼αK K∼αD))
... | no ¬K∼αB = α-step (lem-seq-app-¬α seqABn seqCKm ¬isAbsB ¬K∼αB) (∼· ∼ρ K∼αD)
lem-seq-app-¬α {C = C} seqABn (β-step {K = K} {n₀ = m'} seqCKm K→Dm' m≤m') ¬isAbsB ¬C∼αD with C ≡α K
... | yes C∼αK = β-step seqACBKn (appNoAbsR K→Dm' ¬isAbsB) (≤-sum-l {z = m'} (seq-redexCount seqABn))
          where seqACBCn = lem-seq-appACBC seqABn ¬isAbsB
                seqACBKn = α-step seqACBCn (∼· ∼ρ C∼αK)
... | no ¬C∼αK = β-step seqACBKm+crB (appNoAbsR K→Dm' ¬isAbsB) (≤-sum m≤m')
          where seqACBKm+crB = lem-seq-app-¬α seqABn seqCKm ¬isAbsB ¬C∼αK

lem-seq-app-abs-¬α : ∀{A B C D n m} -> seqβ-st A B n -> seqβ-st C D m -> isAbs B -> ¬ (C ∼α D)
                                                           -> seqβ-st (A · C) (B · D) (suc (m + countRedexes B))
lem-seq-app-abs-¬α seqABn single isAbsB ¬C∼αD = ⊥-elim (¬C∼αD ∼ρ)
lem-seq-app-abs-¬α {C = C} seqABn (α-step {K = K} seqCKm K∼αD) isAbsB ¬C∼αD with C ≡α K
... | yes C∼αK = ⊥-elim (¬C∼αD (∼τ C∼αK K∼αD))
... | no ¬K∼αB =  α-step (lem-seq-app-abs-¬α seqABn seqCKm isAbsB ¬K∼αB) (∼· ∼ρ K∼αD)
lem-seq-app-abs-¬α {A} {B} {C} seqABn (β-step {K = K} {n = m}{n₀ = m'} seqCKm K→Dm' m≤m') isAbsB ¬C∼αD with C ≡α K | lem-seq-appACBC-abs {C = C} seqABn isAbsB
... | yes C∼αK | ∨-intro₁ seqACBCn = β-step (α-step seqACBCn (∼· ∼ρ C∼αK)) (appAbsR K→Dm' isAbsB) (≤-sum-l {z = suc m'} (seq-redexCount seqABn))   
... | yes C∼αK | ∨-intro₂ seqACBCsucn = β-step (α-step seqACBCsucn (∼· ∼ρ C∼αK)) (appAbsR K→Dm' isAbsB) (s≤s (≤-sum-l {z = m'} (seq-redexCount seqABn)))
... | no ¬C∼αK | ∨-intro₁ seqACBCn = β-step seqACBKsucm+crB (appAbsR K→Dm' isAbsB) (s≤s (≤-sum m≤m'))
               where seqACBKsucm+crB = lem-seq-app-abs-¬α seqABn seqCKm isAbsB ¬C∼αK
... | no ¬C∼αK | ∨-intro₂ seqACBCsucn = β-step seqACBKsucm+crB (appAbsR K→Dm' isAbsB) (s≤s (≤-sum m≤m'))
               where seqACBKsucm+crB = lem-seq-app-abs-¬α seqABn seqCKm isAbsB ¬C∼αK

lem-leftmost→seqβstl : ∀{M N} -> M ⟶l N -> seqβ-st M N 0
lem-leftmost→seqβstl MβN = β-step single MβN (z≤n)

lem-leftmost→seqβst : ∀{M N} -> M →→l N -> seqβ-st M N 0
lem-leftmost→seqβst refl = single
lem-leftmost→seqβst (α-step M→→lK K~N) = α-step (lem-leftmost→seqβst M→→lK) K~N
lem-leftmost→seqβst (append M→→lK K⟶lN) = append-seq0 (lem-leftmost→seqβst M→→lK) (lem-leftmost→seqβstl K⟶lN)

hap→seqβst : ∀{M N} -> M →→hap N -> seqβ-st M N 0
hap→seqβst MhapN = lem-leftmost→seqβst (hap→l MhapN)

st→seqβst : ∀{M N} -> M →→st N -> Σₓ ℕ (\n -> seqβ-st M N n)
st→seqβst {M} {v x} (st-var M→hapx) = ( 0 , lem-leftmost→seqβst (hap→l M→hapx))
st→seqβst (st-app {A} {B} {C} {D} L→→hapAB A→→stC B→→stD) with st→seqβst A→→stC | st→seqβst B→→stD | isAbs? C | B ≡α D
... | (m , seqACm) | (n , seqBDn) | no ¬isAbsC | yes B∼αD = (m , append-seq0 seqLAB0 seqABCDm)
                   where seqLAB0 = lem-leftmost→seqβst (hap→l L→→hapAB)
                         seqABCBm = lem-seq-appACBC {C = B} seqACm ¬isAbsC
                         seqABCDm = α-step seqABCBm (∼· ∼ρ B∼αD)
... | (m , seqACm) | (n , seqBDn) | no ¬isAbsC | no ¬B∼αD = (n + countRedexes C , append-seq0 seqLAB0 seqABCDn+crC)
                   where seqLAB0 = lem-leftmost→seqβst (hap→l L→→hapAB)
                         seqABCDn+crC = lem-seq-app-¬α seqACm seqBDn ¬isAbsC ¬B∼αD
... | (m , seqACm) | (n , seqBDn) | yes isAbsC | no ¬B∼αD = ( suc (n + countRedexes C) , append-seq0 seqLAB0 (lem-seq-app-abs-¬α seqACm seqBDn isAbsC ¬B∼αD))
                   where seqLAB0 = lem-leftmost→seqβst (hap→l L→→hapAB)  
... | (m , seqACm) | (n , seqBDn) | yes isAbsC | yes B∼αD with lem-seq-appACBC-abs {C = B} seqACm isAbsC
... | ∨-intro₁ seqABCBn = (m , append-seq0 seqLAB0 (α-step seqABCBn (∼· ∼ρ B∼αD)))
                   where seqLAB0 = lem-leftmost→seqβst (hap→l L→→hapAB)
... | ∨-intro₂ seqABCBsucn = (suc m , append-seq0 seqLAB0 (α-step seqABCBsucn (∼· ∼ρ B∼αD)))
                   where seqLAB0 = lem-leftmost→seqβst (hap→l L→→hapAB)
st→seqβst (st-abs {x} L→→hapA A→→stB) with st→seqβst A→→stB
... | (n , seq) = (n , append-seq0 (lem-leftmost→seqβst (hap→l L→→hapA)) (abs-seq {x} seq))
st→seqβst (st-alpha L→→stA' A'~αA) with st→seqβst L→→stA'
... | (n , seq) = (n , α-step seq A'~αA) 

-- Lemma 3.4
-- (1)
st-refl : ∀{M} -> M →→st M
st-refl {v x} = st-var refl
st-refl {A · B} = st-app refl (st-refl {A}) (st-refl {B})
st-refl {ƛ x A} = st-abs refl (st-refl {A})

-- (2)
hap-app-r : ∀{M N P} -> M →→hap N -> M · P →→hap N · P
hap-app-r refl = refl
hap-app-r (α-step M→→hapN' N'~N) = α-step (hap-app-r M→→hapN') (∼· N'~N ∼ρ)
hap-app-r (append M→→hapK K⟶hapN) = append (hap-app-r M→→hapK) (hap-chain K⟶hapN)

st-app-r : ∀{M M' N N'} -> M →→st M' -> N →→st N' -> M · N →→st M' · N'
st-app-r (st-var x₁) y = st-app refl (st-var x₁) y
st-app-r (st-app x x₁ x₂) y = st-app refl (st-app x x₁ x₂) y
st-app-r (st-abs x₁ x₂) y = st-app refl (st-abs x₁ x₂) y
st-app-r (st-alpha x x₁) y = st-app refl (st-alpha x x₁) y

-- (3)
hap-st→st : ∀{L M N} -> L →→hap M -> M →→st N -> L →→st N
hap-st→st L→→hapM (st-var M→→hapx) = st-var (α-star-trans L→→hapM M→→hapx)
hap-st→st L→→hapM (st-app M→→hapAB A→→stC B→→stD) = st-app (α-star-trans L→→hapM M→→hapAB) A→→stC B→→stD
hap-st→st L→→hapM (st-abs M→→hapλxA A→→stB) = st-abs (α-star-trans L→→hapM M→→hapλxA) A→→stB
hap-st→st L→→hapM (st-alpha M→→stA' A'~αA) = st-alpha (hap-st→st L→→hapM M→→stA') A'~αA

lem-hap-subst : ∀{σ M N} -> M ⟶hap N ->  Σₓ Λ (λ N' -> ((M ∙ σ) ⟶hap N') ∧ (N' ∼α (N ∙ σ)))
lem-hap-subst {σ} (hap-head {x} {A} {B}) = ( (A ∙ σ') ∙ (ι ≺+ (y , B ∙ σ)) , ∧-intro λyAσ'·Bσ⟶hapAσ'y,Bσ (subst₂ _∼α_ refl (corollary1Prop7 {A} {B} {x = x}) Aσ'Bσ))
                             where y = χ (σ , ƛ x A)
                                   σ' = σ ≺+ (x ∶ v y)
                                   λyAσ'·Bσ⟶hapAσ'y,Bσ = hap-head {y} {A ∙ σ'} {B ∙ σ}
                                   Aσ'Bσ : (A ∙ σ') ∙ (ι ≺+ (y , B ∙ σ)) ∼α (A ∙ σ  ≺+ (x , B ∙ σ))
                                   Aσ'Bσ = corollary1SubstLemma {x}{χ (σ , ƛ x A)}{M = A}{N = B ∙ σ} (χ-lemma2 σ (ƛ x A))
lem-hap-subst {σ} (hap-chain {C = P} A⟶hapB) with lem-hap-subst A⟶hapB
... | (N' , Aσ─>N'∧N'~Bσ) = (N' · (P ∙ σ) , ∧-intro (hap-chain (∧-elim-l Aσ─>N'∧N'~Bσ)) (∼· (∧-elim-r Aσ─>N'∧N'~Bσ) ∼ρ))

hap-single : ∀{M N} -> M ⟶hap N -> M →→hap N 
hap-single = append refl

hap-subst : ∀{M N σ} -> M →→hap N -> (M ∙ σ) →→hap (N ∙ σ)
hap-subst refl = refl
hap-subst (α-step M→→hapN' N'~N) = α-step (hap-subst M→→hapN') (≡→α (lemmaM∼M'→Mσ≡M'σ N'~N))
hap-subst {M} {N} {σ} (append {K = K} M→→hapK K⟶hapN) =
  α-star-trans (hap-subst M→→hapK) (α-step (α-star-singl Kσ⟶N') N'~Nσ) 
                  where N' : Λ
                        N' = proj₁ (lem-hap-subst K⟶hapN)
                        Kσ⟶N' : (K ∙ σ) ⟶hap N'
                        Kσ⟶N' = ∧-elim-l (proj₂ (lem-hap-subst K⟶hapN))
                        N'~Nσ : N' ∼α (N ∙ σ) 
                        N'~Nσ = ∧-elim-r (proj₂ (lem-hap-subst K⟶hapN))

infix 1 _→st_
_→st_ : Σ → Σ → Set
σ →st σ' = (x : V) → σ x →→st σ' x

ι≅ι : ι →st ι
ι≅ι x = st-var refl

≅-append : ∀{σ σ' M N x} -> σ →st σ' -> M →→st N -> σ ≺+ (x , M) →st  σ' ≺+ (x , N)
≅-append {σ} {σ'} {M} {N} {x} σ≅σ' M→→stN var with x ≟ var
... | yes _ = M→→stN
... | no _  = σ≅σ' var 

st-exist : ∀{M N} -> M →→st N -> Σₓ Λ (λ N' -> (M →→st N') ∧ (N' ∼α N))
st-exist {N = N} M→→stN = (N , ∧-intro M→→stN ∼ρ)

st-substσ≅σ' : ∀{M N σ σ'} -> M →→st N -> σ →st σ' -> M ∙ σ →→st N ∙ σ'
st-substσ≅σ' {M} {.(v _)} {σ} {σ'} (st-var {x} M→→hapx) σ→stσ' = hap-st→st Mσ→→hapσx (σ→stσ' x)
                                           where Mσ→→hapσx = hap-subst {σ = σ} M→→hapx
st-substσ≅σ' {M} {.(_ · _)} {σ} {σ'} (st-app M→→hapAB A→→stC B→→stD) σ→stσ'
                 = st-app (hap-subst {σ = σ} M→→hapAB) AC BD
                                           where AC = st-substσ≅σ' A→→stC σ→stσ'
                                                 BD = st-substσ≅σ' B→→stD σ→stσ'
st-substσ≅σ' {M} {A} {σ} {σ'} (st-alpha M→→stA' A'~αA) σ→stσ' = st-alpha (st-substσ≅σ' M→→stA' σ→stσ') (≡→α (lemmaM∼M'→Mσ≡M'σ A'~αA))
st-substσ≅σ' {M} {.(ƛ _ _)} {σ} {σ'} (st-abs {x} {A} {B} M→→hapλxA A→→stB) σ→stσ' = st-alpha Mσ→→stλzBσz' z∼αx 
                                           where Mσ→→hapλyₐAσ₁ = hap-subst {σ = σ} M→→hapλxA
                                                 yₐ = χ (σ , ƛ x A)
                                                 yb = χ (σ' , ƛ x B)
                                                 yz = χ (ι , ((ƛ x A) ∙ σ) · ((ƛ x B) ∙ σ'))
                                                 σ₁ = σ ≺+ (x , v yₐ)
                                                 σz = σ ≺+ (x , v yz)
                                                 σ₁' = σ' ≺+ (x , v yb)
                                                 σz' = σ' ≺+ (x , v yz)
                                                 #app : ∀{x A B} -> x # (A · B) -> (x # A) ∧ (x # B)
                                                 #app (#· x#A x#B) = ∧-intro x#A x#B 
                                                 #zA : yz # (ƛ x A) ∙ σ
                                                 #zA =  ∧-elim-l (#app (lemma-χι (((ƛ x A) ∙ σ) · ((ƛ x B) ∙ σ'))))
                                                 #zB : yz # (ƛ x B) ∙ σ'
                                                 #zB = ∧-elim-r (#app (lemma-χι (((ƛ x A) ∙ σ) · ((ƛ x B) ∙ σ'))))
                                                 g : (A ∙ σ₁) ∙ ι ≺+ (yₐ ∶ v yz) ∼α (A ∙ σz) ∙ ι ≺+ (yz ∶ v yz)
                                                 g = ∼τ (corollary1SubstLemma {x}{yₐ}{σ}{A} (χ-lemma2 σ (ƛ x A)))
                                                        (∼τ (lemma∙ι {A ∙ σz}) (≡→α (sym (lemmaMι≺+x,x {yz} {A ∙ σz}))))
                                                 λyₐAσ₁∼αλzAσz = ∼ƛ {A ∙ σ₁} {A ∙ σz} {yₐ} {yz} {yz} #zA #ƛ≡ g
                                                 Mσ→→hapλzAσz = α-step Mσ→→hapλyₐAσ₁ λyₐAσ₁∼αλzAσz
                                                 σz≅σz' : σz →st σz'
                                                 σz≅σz' var with x ≟ var
                                                 ... | yes var≡x = st-refl
                                                 ... | no  var≠x = σ→stσ' var
                                                 Aσz→→stBσz' = st-substσ≅σ' A→→stB σz≅σz'
                                                 Mσ→→stλzBσz' = st-abs Mσ→→hapλzAσz Aσz→→stBσz'
                                                 z∼αx :  ƛ yz (B ∙ σz') ∼α (ƛ x B) ∙ σ'
                                                 z∼αx = ∼ƛ #ƛ≡ #zB (∼σ (∼τ (corollary1SubstLemma {x}{yb}{σ'}{B} (χ-lemma2 σ' (ƛ x B))) (∼τ (lemma∙ι {B ∙ σz'}) (≡→α (sym (lemmaMι≺+x,x {yz} {B ∙ σz'}))))))

st-alpha-abs : ∀{P x M} -> P →→st ƛ x M -> Σₓ Λ (\M' -> (Σₓ V (\x' -> Σₓ Λ (\M'' -> ((P →→hap ƛ x' M') ∧ (M' →→st M'')) ∧ (ƛ x' M'' ∼α ƛ x M)))))
st-alpha-abs (st-abs {x} {M'} {M} P→→hapλxM' M'→→stM) = (M' , (x , (M , ∧-intro (∧-intro P→→hapλxM' M'→→stM) ∼ρ)))
st-alpha-abs (st-alpha P→→stλx'M' (∼ƛ y#λx'M' y#λxM M'x',y~Mx,y)) with st-alpha-abs P→→stλx'M'
... | (M' , (x' , (M'' , ∧-intro (∧-intro P→→hapλx'M' M'→→stM'') λx'M''~λxM))) = (M' , (x' , (M'' , ∧-intro (∧-intro P→→hapλx'M' M'→→stM'') (∼τ λx'M''~λxM (∼ƛ y#λx'M' y#λxM M'x',y~Mx,y)))))

st-abs-subst : ∀ {L M N x} -> L →→st (ƛ x M) · N -> L →→st (M [ x := N ])
st-abs-subst {L} {M} {N} {x} (st-app {P} {N'} L→→hapPN' P→→stλxM N'→→stN) with (st-substσ≅σ' M'→→stM (≅-append {x = x'} ι≅ι N'→→stN))
  where M'→→stM = ∧-elim-r (∧-elim-l (proj₂ (proj₂ (proj₂ (st-alpha-abs P→→stλxM)))))
        x' = proj₁ (proj₂ (st-alpha-abs P→→stλxM))
... | Hst = st-alpha (hap-st→st (α-star-trans (α-star-trans L→→hapPN' (hap-app-r {P}{ƛ x' M'}{N'} P→→hapλx'M')) (append refl (hap-head {x'} {M'} {N'}))) Hst) M''x',N~Mx,N
  where M'→→stM = ∧-elim-r (∧-elim-l (proj₂ (proj₂ (proj₂ (st-alpha-abs P→→stλxM)))))
        x' = proj₁ (proj₂ (st-alpha-abs P→→stλxM))
        M' = proj₁ (st-alpha-abs P→→stλxM)
        P→→hapλx'M' = ∧-elim-l (∧-elim-l (proj₂ (proj₂ (proj₂ (st-alpha-abs P→→stλxM)))))
        M'' = proj₁ (proj₂ (proj₂ (st-alpha-abs P→→stλxM)))
        M''x',N~Mx,N : (M'' [ x' := N ]) ∼α (M [ x := N ])
        M''x',N~Mx,N with ∧-elim-r (proj₂ (proj₂ (proj₂ (st-alpha-abs P→→stλxM))))
        ... | (∼ƛ {y = y}  y#λx'M'' y#λxM M''x',y~Mx,y) = ∼τ (∼σ (corollary1SubstLemma {x'}{y}{ι}{M''}{N} (lemma#→ι#⇂ y#λx'M''))) (∼τ (≡→α (lemmaM∼M'→Mσ≡M'σ {σ = (ι ≺+ (y , N))} M''x',y~Mx,y)) (corollary1SubstLemma {x}{y}{ι}{M}{N} (lemma#→ι#⇂ y#λxM)))
st-abs-subst {L} {M} {N} {x} (st-alpha {(ƛ y M') · N'} L→→stλyM'N' (∼· (∼ƛ {y = w} p q rs) N'~N)) = st-alpha (st-abs-subst L→→stλyM'N') (∼τ M'y,N'~MxN' (lemma-subst {M = M} ∼ρ x,N'~xN))
  where lem-α-both : ∀{M N M' N'} -> M ∼α N -> M ∼α M' -> N ∼α N' -> M' ∼α N'
        lem-α-both M~N M~M' N~N' = ∼τ (∼τ (∼σ M~M') (M~N)) N~N'
        M'y,N'~MxN' : (M' [ y := N' ]) ∼α (M [ x := N' ])
        M'y,N'~MxN' = lem-α-both (≡→α (lemmaM∼M'→Mσ≡M'σ {σ = ι ≺+ (w , N')} rs)) (corollary1SubstLemma {y} {w} {ι} {M = M'} (lemma#→ι#⇂ p)) (corollary1SubstLemma {x} {w} {ι} {M = M} (lemma#→ι#⇂ q))
        x,N'~xN : ι ≺+ (x ∶ N') ∼α ι ≺+ (x ∶ N) ⇂ M
        x,N'~xN w w*M with x ≟ w
        ... | yes _ = N'~N
        ... | no _ = ∼v

st-β→st : ∀{L M N} -> L →→st M -> M ⟶β N -> L →→st N
st-β→st L→→stM M⟶βN with proj₂ M⟶βN
... | outer-redex = st-alpha N' ∼ρ 
                      where N' = st-abs-subst L→→stM
st-β→st (st-app {D = C} L→→hapA'C' A'→→stA C'→→stC) M⟶βN | (appNoAbsL {n = n} A⟶B↧n _)
                                                 = st-app L→→hapA'C' A'B C'→→stC
                                             where A'B = st-β→st A'→→stA ( n , A⟶B↧n)
st-β→st (st-alpha L→→stM' M'αM) M⟶βN | _ = st-alpha (st-β→st L→→stM' N') N'αN
                                           where N' = ∧-elim-l (proj₂ (lem-βα M⟶βN (∼σ M'αM)))
                                                 N'αN = ∧-elim-r (proj₂ (lem-βα M⟶βN (∼σ M'αM)))
st-β→st (st-app {D = C} L→→hapA'C' A'→→stA C'→→stC) M⟶βN | (appAbsL {n = n} A⟶B↧n _)
                                                 = st-app L→→hapA'C' A'B C'→→stC
                                             where A'B = st-β→st A'→→stA ( n , A⟶B↧n)
st-β→st (st-app {C = C} L→→hapC'A' C'→→stC A'→→stA) M⟶βN |  (appNoAbsR {n = n} A⟶B↧n _)
                                                 = st-app L→→hapC'A' C'→→stC A'B
                                             where A'B = st-β→st A'→→stA ( n , A⟶B↧n)
st-β→st (st-app {C = C} L→→hapC'A' C'→→stC A'→→stA) M⟶βN |  (appAbsR {n = n} A⟶B↧n _)
                                                 = st-app L→→hapC'A' C'→→stC A'B
                                             where A'B = st-β→st A'→→stA ( n , A⟶B↧n)
st-β→st (st-abs {x = x} L→→hapA A→→stB) M⟶βN | (abs {n = n} A⟶B↧n) = st-abs L→→hapA A'B
                                             where A'B = st-β→st A→→stB ( n , A⟶B↧n)

-- Lemma 3.7
β→st : ∀{M N} -> M →→β N -> M →→st N
β→st {M} refl = st-refl 
β→st (α-step M→→βN' N'~N) = st-alpha (β→st M→→βN') N'~N
β→st (append M→→βK K⟶βN) with β→st M→→βK
... | M→→stK = st-β→st M→→stK K⟶βN

standardization : ∀{M N} -> M →→β N -> Σₓ ℕ (λ n -> seqβ-st M N n)
standardization M→→βN = st→seqβst (β→st M→→βN)

lem-sum-l : ∀{a b} -> a + b ≡ 0 -> a ≡ 0
lem-sum-l {zero} {b} zero+b≡0 = refl
lem-sum-l {suc _} ()

lem-sum-r : ∀{a b} -> a + b ≡ 0 -> b ≡ 0
lem-sum-r {zero} {b} zero+b≡0 = zero+b≡0
lem-sum-r {suc _} ()

lem-sum-zero : ∀{a b} -> a ≡ 0 -> b ≡ 0 -> a + b ≡ 0
lem-sum-zero refl refl = refl

lem-crabs : ∀{x A} -> countRedexes (ƛ x A) ≡ countRedexes A
lem-crabs = refl

isAbsA→isAbsAσ : ∀{A σ} -> isAbs A -> isAbs (A ∙ σ)
isAbsA→isAbsAσ {v x} ()
isAbsA→isAbsAσ {A · A₁} ()
isAbsA→isAbsAσ {ƛ x A} isAbsA = abs 

-- onlyVars-¬isAbs
-- no se cumple, se cumple solo con onlyvars como pre y ya lo probaste!
isAbsAσ→isAbsA : ∀{A σ} -> onlyVars σ -> isAbs (A ∙ σ) -> isAbs A 
isAbsAσ→isAbsA {A} {σ} onlyVarsσ isAbsAσ with isAbs? A
... | yes isAbsA = isAbsA
... | no ¬isAbsA = ⊥-elim ((onlyVars-¬isAbs {σ = σ} onlyVarsσ ¬isAbsA) isAbsAσ)

lem-sum-ab : ∀{a b c d} -> a ≡ b -> c ≡ d -> a + c ≡ b + d
lem-sum-ab refl refl = refl
 
crAιx,y≡crA : ∀{σ A} -> onlyVars σ -> countRedexes (A ∙ σ) ≡ countRedexes A
crAιx,y≡crA {σ} {v w} onlyVarsσ with onlyVarsσ w
... | (x , σw=x) = cong countRedexes σw=x
crAιx,y≡crA {σ} {A · B} onlyVarsσ with isAbs? A | isAbs? (A ∙ σ)
... | yes _ | yes _ = cong suc (lem-sum-ab (crAιx,y≡crA {σ} {A} onlyVarsσ) (crAιx,y≡crA {σ} {B} onlyVarsσ))
... | no ¬isAbsA | yes isAbsAσ = ⊥-elim (¬isAbsA (isAbsAσ→isAbsA onlyVarsσ isAbsAσ))
... | yes isAbsA | no ¬isAbsAσ = ⊥-elim (¬isAbsAσ (isAbsA→isAbsAσ isAbsA))
... | no _ | no _ = lem-sum-ab (crAιx,y≡crA {σ} {A} onlyVarsσ) (crAιx,y≡crA {σ} {B} onlyVarsσ)
crAιx,y≡crA {σ}{ƛ w A} onlyVarsσ = crAιx,y≡crA {A = A} (onlyVars-append {σ} {w} onlyVarsσ)

lem-crα : ∀{A B} -> A ∼α B -> countRedexes A ≡ countRedexes B
lem-crα ∼v = refl
lem-crα (∼· {A} {A'} {B} {B'} A~B A~B₁) with isAbs? A | isAbs? A'
... | yes _ | yes _ = cong suc (lem-sum-ab (lem-crα A~B) (lem-crα A~B₁))
... | yes isAbsA | no ¬isAbsA' = ⊥-elim (¬isAbsA' (isAbsα isAbsA (∼σ A~B)))
... | no ¬isAbsA | yes isAbsA' = ⊥-elim (¬isAbsA (isAbsα isAbsA' A~B))
... | no _ | no _ = lem-sum-ab (lem-crα A~B) (lem-crα A~B₁)
lem-crα (∼ƛ {A} {B} {x} {x'} y#A y#B Ax,y~Bw,y) = subst₂ _≡_ (crAιx,y≡crA {A = A}(onlyVars-append {x = x} ιonlyVars)) (crAιx,y≡crA {A = B} (onlyVars-append {x = x'} ιonlyVars)) (lem-crα Ax,y~Bw,y)

lem-l' : ∀{M N n} -> M β N ↧ n -> countRedexes N ≡ zero -> n ≡ 0
lem-l' outer-redex crN≡0 = refl
lem-l' (appNoAbsL {n} {A} {B} AβBn ¬isAbsA) with isAbs? B
... | yes isAbsB = λ ()
... | no ¬isAbsB = λ crB+crC≡0 -> lem-l' AβBn (lem-sum-l crB+crC≡0)
lem-l' (appAbsL {n} {A} {B} AβBn isAbsA) with isAbs? B
... | yes isAbsB = λ ()
... | no ¬isAbsB = λ crB+crC≡0 -> ⊥-elim ((β-abs AβBn ¬isAbsB) isAbsA)
lem-l' (appNoAbsR {n} {A} {B} {C} AβBn ¬isAbsC) with isAbs? C
... | yes isAbsC = ⊥-elim (¬isAbsC isAbsC)
... | no _ = λ crC+crB≡0 -> lem-sum-zero (lem-l' AβBn (lem-sum-r {countRedexes C} crC+crB≡0)) (lem-sum-l crC+crB≡0)
lem-l' (appAbsR {n} {A} {B} {C} AβBn isAbsC) with isAbs? C
... | yes _ = λ ()
... | no ¬isAbsC = ⊥-elim (¬isAbsC isAbsC)
lem-l' (abs x₁) crN≡0 = lem-l' x₁ crN≡0

subst₃ : ∀ {a b c p} {A : Set a} {B : Set b} {C : Set c} (P : A → B → C → Set p)
         {x₁ x₂ z₁ y₁ y₂ z₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ -> P x₁ y₁ z₁  → P x₂ y₂ z₂
subst₃ P refl refl refl p = p


seqβ0→l : ∀ {A B} -> seqβ-st A B 0 -> A →→l B
seqβ0→l single = refl
seqβ0→l (α-step seqAB0 x) = α-step (seqβ0→l seqAB0) x
seqβ0→l (β-step {n = zero} seqAB0 AβBn n<=0) = append (seqβ0→l seqAB0) AβBn
seqβ0→l (β-step {n = suc _} seqAB0 AβBn ())

lem≤0 : ∀{a} -> a ≤ 0 -> a ≡ 0
lem≤0 {zero} _ = refl
lem≤0 {suc _} ()

seqst→l : ∀{A B n} -> seqβ-st A B n -> countRedexes B ≡ 0 -> A →→l B
seqst→l single crB≡0 = refl
seqst→l (α-step seqβAKn K~B) crB≡0 = α-step (seqst→l seqβAKn (subst₂ _≡_ (sym (lem-crα K~B)) refl crB≡0)) K~B
      where seqst→β : ∀{M N n} -> seqβ-st M N n -> M →→β N
            seqst→β single = refl
            seqst→β (α-step x x₁) = α-step (seqst→β x) x₁
            seqst→β {n = n} (β-step x x₁ x₂) = append (seqst→β x) (n ∶ x₁) 
seqst→l {A} (β-step {K} {n} {n'} {B} seqβAKn KβBn' n<=n') crB≡0 = append A→→lK K⟶lB
      where n'≡0 : n' ≡ 0
            n'≡0 = lem-l' KβBn' crB≡0
            n≡0 : n ≡ 0
            n≡0 = lem≤0 (subst₂ _≤_ refl n'≡0 n<=n')
            seqβstAK0 : seqβ-st A K 0
            seqβstAK0 = subst₃ seqβ-st refl refl n≡0 seqβAKn
            A→→lK : A →→l K
            A→→lK = seqβ0→l seqβstAK0
            K⟶lB : K ⟶l B
            K⟶lB = subst₃ _β_↧_ refl refl n'≡0 KβBn'

leftmost-nf : ∀{A B} -> A →→β B -> countRedexes B ≡ 0 -> A →→l B
leftmost-nf A→→βB crB≡0 = seqst→l (proj₂ (standardization A→→βB)) crB≡0
\end{code}
