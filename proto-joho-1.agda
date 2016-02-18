module proto-joho-1 where

-- Agda の注意 : ファイル名の先頭にアラビア数字は使えない，
--              ファイル名にアンダースコアは使えない

-- 情報科学における論理を Agda で書いてみる．
-- 形式化には，武山さんのコードと
--
-- https://sites.google.com/a/progsci.info.kanagawa-u.ac.jp/kinoshita-yoshiki-lab/nyusu/2015nianxiahesuxiangxijuemaru/BDT.hs?attredirects=0&d=1
--
-- 木下修司さんのコード
--  
-- https://github.com/kino3/toys/blob/master/agda/Logic-in-IS.agda
-- 　
-- 神大木下佳樹研2015年春合宿の Logic.agda
--
-- https://github.com/falke727/lernen/blob/master/agda/kinoshitalab/20150302/Logic.agda
--
-- を参考にした．

data Bool : Set where
 t : Bool
 f : Bool

not : Bool → Bool
not t = f
not f = t

_and_ : Bool → Bool → Bool
t and q = q
f and q = f

_or_ : Bool → Bool → Bool
t or q = t
f or q = q

_imp_ : Bool → Bool → Bool
t imp q = q
f imp q = t

infix  100 not
infixr 90  _and_
infixr 80  _or_
infixr 70  _imp_

-- 命題 (proposition)，命題は無限にあるものと考える．
open import Data.Nat
prop = ℕ

-- 命題論理式 (proposional formula)
data pform : Set where  
  var : prop → pform
  _∧_ : pform → pform → pform
  _∨_ : pform → pform → pform
  _⊃_ : pform → pform → pform
  ¬_  : pform → pform
  ⊤   : pform
  ⊥   : pform

infix  10 ¬_
infixr 9  _∧_
infixr 8  _∨_
infixr 7  _⊃_

-- 付値 (assignment)
assign = prop → Bool

-- 付値の論理式への拡張
_⟦_⟧ : assign → pform → Bool
v ⟦ var p ⟧ = v p
v ⟦ p ∧ q ⟧ = (v ⟦ p ⟧) and (v ⟦ q ⟧)
v ⟦ p ∨ q ⟧ = (v ⟦ p ⟧) or  (v ⟦ q ⟧)
v ⟦ p ⊃ q ⟧ = (v ⟦ p ⟧) imp (v ⟦ q ⟧)
v ⟦ ¬ p ⟧ = not (v ⟦ p ⟧)
v ⟦ ⊤  ⟧ = t
v ⟦ ⊥ ⟧ = f

-- isTautology : pform → Set
-- isTautology A = (v : assign) → v ⟦ A ⟧ == t

open import Relation.Binary.PropositionalEquality 
  renaming (_≡_ to _≈_) hiding ([_]) 
open import Relation.Binary.Core using (_≡_; _≢_; refl)

isTautology : assign → pform → Set
isTautology v A = v ⟦ A ⟧ ≡ t

open import Relation.Nullary using (yes; no; Dec) renaming (¬_ to Not_)

-- 定理1.1 与えられた論理式がトートロジーか否かは決定可能である．
theorem1-1 : (v : assign) (A : pform) → Dec (isTautology v A)
theorem1-1 v (var p) with v p
theorem1-1 v (var p) | t = yes refl
theorem1-1 v (var p) | f = no (λ ())
theorem1-1 v (A ∧ B) with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-1 v (A ∧ B) | t | t = yes refl
theorem1-1 v (A ∧ B) | t | f = no (λ ())
theorem1-1 v (A ∧ B) | f | _ = no (λ ())
theorem1-1 v (A ∨ B) with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-1 v (A ∨ B) | f | f = no (λ ())
theorem1-1 v (A ∨ B) | f | t = yes refl
theorem1-1 v (A ∨ B) | t | _ = yes refl
theorem1-1 v (A ⊃ B) with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-1 v (A ⊃ B) | t | t = yes refl
theorem1-1 v (A ⊃ B) | t | f = no (λ ())
theorem1-1 v (A ⊃ B) | f | _ = yes refl
theorem1-1 v (¬ A) with v ⟦ A ⟧
theorem1-1 v (¬ A) | t = no (λ ())
theorem1-1 v (¬ A) | f = yes refl
theorem1-1 v ⊤  = yes refl
theorem1-1 v ⊥ = no (λ ())

open import Data.Product using (Σ; _,_; _×_)

isSatisfiable : pform → Set
isSatisfiable A = Σ assign (λ v → (v ⟦ A ⟧) ≡ t)

-- 充足可能な論理式の例； 0 1 は命題変数である．
R : isSatisfiable (¬ (var 0) ∧ (var 1))
R = u , refl
  where
    u : prop → Bool
    u 0 = f
    u 1 = t
    u _ = t

-- A は B の必要十分条件である．
_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)
infix 0 _⇔_

isNotSatisfiable' : assign → pform → Set
isNotSatisfiable' v A = v ⟦ A ⟧ ≡ f

isNotSatisfiable : assign → pform → Set
isNotSatisfiable v A = v ⟦ A ⟧ ≢ t

INS' = isNotSatisfiable'
INS = isNotSatisfiable

open import Data.Empty
open import Relation.Nullary.Negation 

INS⇒INS' : {v : assign} → {A : pform} → INS' v A → INS v A 
INS⇒INS' {v} {A} prf with v ⟦ A ⟧
INS⇒INS' ()  | t
INS⇒INS' prf | f = λ ()

INS'⇒INS : {v : assign} → {A : pform} → INS v A → INS' v A 
INS'⇒INS {v} {A} prf with v ⟦ A ⟧
INS'⇒INS prf | t = ⊥-elim (prf refl)
INS'⇒INS prf | f = refl

-- INS⇒INS' の別証明
--
-- INS⇒INS' : {v : assign} → {A : pform} → INS' v A → INS v A 
-- INS⇒INS' {v} {A} prf = λ x → contradiction x (lemma {v} {A} prf)
-- lemma : ∀ {v A} → v ⟦ A ⟧ ≡ f → v ⟦ A ⟧ ≡ t → Data.Empty.⊥
-- lemma {v} {A}  prf1 prf2 with v ⟦ A ⟧
-- lemma ()   prf2 | t
-- lemma prf1 ()   | f

-- 定理1.2 論理式Aが充足不可能であるための必要十分条件は¬Aがトートロジーとなることである．
theorem1-2 : (v : assign) → (A : pform) → isNotSatisfiable v A ⇔ isTautology v (¬ A) 
theorem1-2 v A with v ⟦ A ⟧
theorem1-2 v A | t = (λ prf → ⊥-elim (prf refl)) , (λ ())
theorem1-2 v A | f = (λ prf → refl) , (λ x ())

-- 問1.1
-- 1) A ⊃ B および A がともに充足可能ならば，B も充足可能である．
-- 反例を与える
e1-1-1' : (v : assign) → Σ pform (λ A → (Σ pform (λ B → (isSatisfiable (A ⊃ B) × (isSatisfiable A) × (isNotSatisfiable v B)))))
e1-1-1' v = var 1 , (var 0 ∧ ¬ var 0) , ((λ x → f) , refl) , ((λ x → t) , refl) , lemma v
  where
    lemma : (v : assign) → v 0 and not (v 0) ≡ t → Data.Empty.⊥
    lemma v with v 0
    lemma v' | t = λ ()
    lemma v' | f = λ ()

-- e1-1-1'' : (v : assign) → Σ[ A ∶ pform ] (Σ[ B ∶ pform ] (isSatisfiable (A ⊃ B) × (isSatisfiable A) × (isNotSatisfiable v B))) → Not ((A B : pform) → isSatisfiable (A ⊃ B) → isSatisfiable A → isSatisfiable B)
-- e1-1-1'' = λ v x x' → {!!}

--e1-1-1 : Not ((A B : pform) → isSatisfiable (A ⊃ B) → isSatisfiable A → isSatisfiable B)
--e1-1-1 = e1-1-1'' e1-1-1'


--hoge : {A : pform} → {v : assign} → isTautology v A → isSatisfiable A
--hoge {A} {v} prf = v , prf

data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : {A : Set} (x : A) → Inspect x
inspect x = it x refl


-- 2) A ⊃ B がトートロジーで A が充足可能ならば，B も充足可能である．
e1-1-2 : (A B : pform) → ((v : assign) → v ⟦ A ⊃ B ⟧ ≡ t) → Σ assign (λ v → v ⟦ A ⟧ ≡ t) → Σ assign (λ v → v ⟦ B ⟧ ≡ t)
e1-1-2 A B prf1 (v , prf) = v , lemma v prf (prf1 v)
  where
    lemma : (u : assign) → u ⟦ A ⟧ ≡ t → ((u ⟦ A ⟧) imp (u ⟦ B ⟧) ≡ t) → (u ⟦ B ⟧) ≡ t
    lemma u prfP prfQ with u ⟦ A ⟧ | u ⟦ B ⟧
    lemma u prfP prfQ | t | t = refl
    lemma u prfP () | t | f
    lemma u prfP prfQ | f | t = refl
    lemma u () prfQ | f | f


-- 問1.2 ((p ∨ q) ⊃ r) ∨ (p ∧ q) の値を f にするには，p,q,r にどのような値の組を与えればよいか．このような値の組をすべて求めよ．
e1-2 : ∀ v p q r → (Dec (v ⟦ (((p ∨ q) ⊃ r) ∨ (p ∧ q)) ⟧ ≡ f))
e1-2 v p q r with v ⟦ p ⟧ | v ⟦ q ⟧ | v ⟦ r ⟧
e1-2 v p q r | t | t | t = no (λ ())
e1-2 v p q r | t | t | f = no (λ ())
e1-2 v p q r | t | f | t = no (λ ())
e1-2 v p q r | t | f | f = yes refl   -- ((t ∨ f) ⊃ f) ∨ (t ∧ f) = f
e1-2 v p q r | f | t | t = no (λ ())
e1-2 v p q r | f | t | f = yes refl   -- ((f ∨ t) ⊃ f) ∨ (f ∧ t) = f
e1-2 v p q r | f | f | t = no (λ ())
e1-2 v p q r | f | f | f = no (λ ())

--isNotSatisfiable : assign → pform → Set
--isNotSatisfiable v A = v ⟦ A ⟧ ≢ t

open import Data.Unit using (⊤)

isTrue : Bool → Set
isTrue t = Data.Unit.⊤
isTrue f = Data.Empty.⊥

-- 問1.3 論理結合子として ⊃ と ∧ のみを含むような論理式はすべて充足可能であることを示せ．
containOnly⊃And∧ : pform → Bool
containOnly⊃And∧ (var x) = t
containOnly⊃And∧ (A ∧ B) = containOnly⊃And∧ A and containOnly⊃And∧ B
containOnly⊃And∧ (A ∨ B) = f
containOnly⊃And∧ (A ⊃ B) = containOnly⊃And∧ A and containOnly⊃And∧ B
containOnly⊃And∧ (¬ A) = f
containOnly⊃And∧ pform.⊤ = f
containOnly⊃And∧ pform.⊥ = f

infix 1 _≈_
_≈_ : pform → pform → pform
A ≈ B = (A ⊃ B) ∧ (B ⊃ A)

-- 問1.4 v(A ≡ B) = t ⇔ v(A) = v(B)
e1-1-4 : {v : assign} {A B : pform} → (v ⟦ (A ≈ B) ⟧ ≡ t) ⇔ (v ⟦ A ⟧ ≡ v ⟦ B ⟧)
e1-1-4 {v} {A} {B} with v ⟦ A ⟧ | v ⟦ B ⟧
e1-1-4 | t | t = (λ _ → refl) , (λ _ → refl)
e1-1-4 | t | f = (λ ()) , (λ ())
e1-1-4 | f | t = (λ ()) , (λ ())
e1-1-4 | f | f = (λ _ → refl) , (λ _ → refl)

-- 問1.5 v(A ≡ B) ≡ v((A ∧ B) ∨ (¬ A ∧ B))
e1-1-5 : {v : assign} {A B : pform} → v ⟦ A ≈ B ⟧ ≡ (v ⟦ (A ∧ B) ∨ (¬ A ∧ ¬ B) ⟧)
e1-1-5 {v} {A} {B} with v ⟦ A ⟧ | v ⟦ B ⟧
e1-1-5 | t | t = refl
e1-1-5 | t | f = refl
e1-1-5 | f | t = refl
e1-1-5 | f | f = refl

-- 定理1.3 次の論理式はそれぞれトートロジーである．
theorem1-3-1-1 : {v : assign} {A : pform} → isTautology v (A ∧ A ≈ A)  -- 冪等律
theorem1-3-1-1 {v} {A} with v ⟦ A ⟧
theorem1-3-1-1 | t = refl
theorem1-3-1-1 | f = refl

theorem1-3-1-2 : {v : assign} {A : pform} → isTautology v (A ∨ A ≈ A)  -- 冪等律
theorem1-3-1-2 {v} {A} with v ⟦ A ⟧
theorem1-3-1-2 | t = refl
theorem1-3-1-2 | f = refl

theorem1-3-2-1 : {v : assign} {A B C : pform} → isTautology v ((A ∧ (B ∧ C)) ≈ ((A ∧ B) ∧ C))  -- 結合律
theorem1-3-2-1 {v} {A} {B} {C} with v ⟦ A ⟧ | v ⟦ B ⟧ | v ⟦ C ⟧
theorem1-3-2-1 | t | t | t = refl
theorem1-3-2-1 | t | f | t = refl
theorem1-3-2-1 | t | t | f = refl
theorem1-3-2-1 | t | f | f = refl
theorem1-3-2-1 | f | _ | _ = refl

theorem1-3-2-2 : {v : assign} {A B C : pform} → isTautology v ((A ∨ (B ∨ C)) ≈ ((A ∨ B) ∨ C))  -- 結合律
theorem1-3-2-2 {v} {A} {B} {C} with v ⟦ A ⟧ | v ⟦ B ⟧ | v ⟦ C ⟧
theorem1-3-2-2 | t | _ | _ = refl
theorem1-3-2-2 | f | t | _ = refl
theorem1-3-2-2 | f | f | t = refl
theorem1-3-2-2 | f | f | f = refl

theorem1-3-3-1 : {v : assign} {A B : pform} → isTautology v ((A ∧ B) ≈ (B ∧ A))  -- 交換律
theorem1-3-3-1 {v} {A} {B} with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-3-3-1 | t | t = refl
theorem1-3-3-1 | t | f = refl
theorem1-3-3-1 | f | t = refl
theorem1-3-3-1 | f | f = refl

theorem1-3-3-2 : {v : assign} {A B : pform} → isTautology v ((A ∨ B) ≈ (B ∨ A))  -- 交換律
theorem1-3-3-2 {v} {A} {B} with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-3-3-2 | t | t = refl
theorem1-3-3-2 | t | f = refl
theorem1-3-3-2 | f | t = refl
theorem1-3-3-2 | f | f = refl

theorem1-3-4-1 : {v : assign} {A B : pform} → isTautology v ((A ∧ (A ∨ B)) ≈ A)  -- 吸収律
theorem1-3-4-1 {v} {A} with v ⟦ A ⟧ 
theorem1-3-4-1 | t = refl
theorem1-3-4-1 | f = refl

theorem1-3-4-2 : {v : assign} {A B : pform} → isTautology v ((A ∨ (A ∧ B)) ≈ A)  -- 吸収律
theorem1-3-4-2 {v} {A} with v ⟦ A ⟧ 
theorem1-3-4-2 | t = refl
theorem1-3-4-2 | f = refl

theorem1-3-5-1 : {v : assign} {A B C : pform} → isTautology v ((A ∨ (B ∧ C)) ≈ ((A ∨ B) ∧ (A ∨ C)))  -- 分配律
theorem1-3-5-1 {v} {A} {B} {C} with v ⟦ A ⟧ | v ⟦ B ⟧ | v ⟦ C ⟧
theorem1-3-5-1 | t | t | t = refl
theorem1-3-5-1 | t | t | f = refl
theorem1-3-5-1 | t | f | t = refl
theorem1-3-5-1 | t | f | f = refl
theorem1-3-5-1 | f | t | t = refl
theorem1-3-5-1 | f | t | f = refl
theorem1-3-5-1 | f | f | t = refl
theorem1-3-5-1 | f | f | f = refl

theorem1-3-5-2 : {v : assign} {A B C : pform} → isTautology v ((A ∧ (B ∨ C)) ≈ ((A ∧ B) ∨ (A ∧ C)))  -- 分配律
theorem1-3-5-2 {v} {A} {B} {C} with v ⟦ A ⟧ | v ⟦ B ⟧ | v ⟦ C ⟧
theorem1-3-5-2 | t | t | t = refl
theorem1-3-5-2 | t | t | f = refl
theorem1-3-5-2 | t | f | t = refl
theorem1-3-5-2 | t | f | f = refl
theorem1-3-5-2 | f | t | t = refl
theorem1-3-5-2 | f | t | f = refl
theorem1-3-5-2 | f | f | t = refl
theorem1-3-5-2 | f | f | f = refl

theorem1-3-6 : {v : assign} {A : pform} → isTautology v (¬ ¬ A ≈ A)
theorem1-3-6 {v} {A} with v ⟦ A ⟧
theorem1-3-6 | t = refl
theorem1-3-6 | f = refl

theorem1-3-7-1 : {v : assign} {A B : pform} → isTautology v ((¬ (A ∨ B)) ≈ (¬ A ∧ ¬ B))  -- De Morgan's Law
theorem1-3-7-1 {v} {A} {B} with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-3-7-1 | t | t = refl
theorem1-3-7-1 | t | f = refl
theorem1-3-7-1 | f | t = refl
theorem1-3-7-1 | f | f = refl

theorem1-3-7-2 : {v : assign} {A B : pform} → isTautology v ((¬ (A ∧ B)) ≈ (¬ A ∨ ¬ B))  -- De Morgan's Law
theorem1-3-7-2 {v} {A} {B} with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-3-7-2 | t | t = refl
theorem1-3-7-2 | t | f = refl
theorem1-3-7-2 | f | t = refl
theorem1-3-7-2 | f | f = refl

-- 問1.6 2) つぎの論理式はトートロジーか．
e1-6-2-1 : {v : assign} {A B C : pform} → isTautology v ((A ⊃ (B ⊃ C)) ≈ ((A ∧ B) ⊃ C))
e1-6-2-1 {v} {A} {B} {C} with v ⟦ A ⟧ | v ⟦ B ⟧ | v ⟦ C ⟧
e1-6-2-1 | t | t | t = refl
e1-6-2-1 | t | t | f = refl
e1-6-2-1 | t | f | t = refl
e1-6-2-1 | t | f | f = refl
e1-6-2-1 | f | t | _ = refl
e1-6-2-1 | f | f | _ = refl

e1-6-2-2 : {v : assign} {A : pform} → Dec (isTautology v (¬ (¬ A ⊃ A)))
e1-6-2-2 {v} {A} with v ⟦ A ⟧
e1-6-2-2 | t = no (λ ())
e1-6-2-2 | f = yes refl

e1-6-2-3 : {v : assign} {A : pform} → isTautology v ((A ⊃ ¬ A) ⊃ ¬ A)
e1-6-2-3 {v} {A} with v ⟦ A ⟧
e1-6-2-3 | t = refl
e1-6-2-3 | f = refl

_~_ : pform → pform → assign → Set
A ~ B = λ x → isTautology x (A ≈ B)

-- 論理式 A と論理式 B が論理的に同値である ⇔ A ≈ B がトートロジーになる．
--
-- 定理1.4 論理的同値性 ~ についてつぎのことがなりたつ．
theorem1-4-1 : (v : assign) → (A : pform) → (A ~ A) v
theorem1-4-1 v A with v ⟦ A ⟧
theorem1-4-1 v A | t = refl
theorem1-4-1 v A | f = refl

theorem1-4-2 : {v : assign} {A B : pform} → (A ~ B) v → (B ~ A) v
theorem1-4-2 {v} {A} {B} prf with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-4-2 prf | t | t = refl
theorem1-4-2 () | t | f
theorem1-4-2 () | f | t
theorem1-4-2 prf | f | f = refl

theorem1-4-3 : {v : assign} {A B C : pform} → ((A ~ B) v) × ((B ~ C) v) → (A ~ C) v
theorem1-4-3 {v} {A} {B} {C} prf with v ⟦ A ⟧ | v ⟦ B ⟧ | v ⟦ C ⟧
theorem1-4-3 prf | t | t | t = refl
theorem1-4-3 (prf1 , ()) | t | t | f
theorem1-4-3 prf | t | f | t = refl
theorem1-4-3 (() , pprf2) | t | f | f
theorem1-4-3 (() , prf2) | f | t | t
theorem1-4-3 prf | f | t | f = refl
theorem1-4-3 (prf1 , ()) | f | f | t
theorem1-4-3 prf | f | f | f = refl

_==_ : ℕ → ℕ → Bool
zero == zero = t
zero == suc y = f
suc x == zero = f
suc x == suc y = x == y

infix 30 replacePropWithPform
replacePropWithPform : pform → prop → pform → pform
replacePropWithPform (var x) p A with x == p
replacePropWithPform (var x) p A | t = A
replacePropWithPform (var x) p A | f = var x
replacePropWithPform (P ∧ Q) p A = replacePropWithPform P p A ∧ replacePropWithPform Q p A
replacePropWithPform (P ∨ Q) p A = replacePropWithPform P p A ∨ replacePropWithPform Q p A
replacePropWithPform (P ⊃ Q) p A = replacePropWithPform P p A ⊃ replacePropWithPform Q p A
replacePropWithPform (¬ P) p A = ¬ replacePropWithPform P p A
replacePropWithPform pform.⊤ p A = pform.⊤
replacePropWithPform pform.⊥ p A = pform.⊥

theorem1-4-4 : {v : assign} (A B C : pform) (p : prop) → ((A ~ B) v) → (((replacePropWithPform C p A) ~ (replacePropWithPform C p B)) v)
theorem1-4-4 A B (var x) p prf with p == x
theorem1-4-4 A B (var x) p prf | t = {!!}
theorem1-4-4 {v} A B (var x) p prf | f = theorem1-4-1 v {!var x!}
theorem1-4-4 A B (P ∧ Q) p prf = {!!}
theorem1-4-4 A B (P ∨ Q) p prf = {!!}
theorem1-4-4 A B (P ⊃ Q) p prf = {!!}
theorem1-4-4 A B (¬ C) p prf = {!!}
theorem1-4-4 A B pform.⊤ p prf = refl
theorem1-4-4 A B pform.⊥ p prf = refl


--theorem1-4-4 
