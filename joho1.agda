module joho1 where

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
-- を参考にしている（木下修司さんのコードは特に参考にしている）．


-- p.2

-- 命題（proposition）の型を定義する．
-- 命題は無限にあるものと考える．
-- よって命題を定義するために Nat 型を定義する．

data Nat : Set where
  Z   : Nat
  Suc : Nat → Nat

-- 先頭を大文字にして Prop とはできないらしい
prop = Nat


-- p.4
-- 命題論理の論理式（propositional forumla）の型を定義する
infix  10 ¬_
infixr  9 _∧_
infixr  8 _∨_
infixr  7 _⊃_

-- このページでは ⊥ と ⊤ は論理式とはしない
data PropForm : Set where
  var : prop → PropForm                -- 命題変数自体は論理式
  _∧_ : PropForm → PropForm → PropForm
  _∨_ : PropForm → PropForm → PropForm
  _⊃_ : PropForm → PropForm → PropForm
  ¬_  : PropForm → PropForm

-- 命題論理式の例 p.4

-- example1-1 : PropForm
-- example1-1 = var p ⊃ (var q ∨ (¬ var r))
-- -- example1-1 = var p ⊃ var q ∨ ¬ var r   -- 括弧を省略するとこうなる
--   where
--     p q r : PropForm
--     p = Z
--     q = Suc Z
--     r = Suc (Suc Z)

-- p.5
-- ブール型とブール型の演算を定義する
data Bool : Set where
  t : Bool
  f : Bool

infix  100 not_
infixr  90 _and_
infixr  80 _or_
infixr  70 _imp_

_and_ : Bool → Bool → Bool -- 論理結合子の記号として ∧ を用いたいので，ここでは ∧ を用いない．
t and y = y
f and _ = f

_or_ : Bool → Bool → Bool -- 論理結合子の記号として ∨ を用いたいので，ここでは ∨ を用いない．
t or _ = t
f or y = y

_imp_ : Bool → Bool → Bool -- 論理結合子の記号として ⊃ を用いたいので，ここでは ⊃ を用いない．
t imp y = y
f imp _ = t

not_ : Bool → Bool -- 論理結合子の記号として ¬ を用いたいので，ここでは ¬ を用いない．
not t = f
not f = t

_xor_ : Bool → Bool → Bool
t xor t = f
t xor f = t
f xor t = t
f xor f = f

-- 付値 (assignment) p.9
Assign = prop → Bool

-- 「P がなりたつための必要充分条件は Q がなりたつことである」 p.9
---- 後で '×' を自力で定義する
open import Data.Product
_⇔_ : Set → Set → Set
P ⇔ Q = (P → Q) × (Q → P)

-- 付値の論理式への拡張
_⟦_⟧ : Assign → PropForm → Bool
v ⟦ var p ⟧ = v p
v ⟦ p ∧ q ⟧ = (v ⟦ p ⟧) and (v ⟦ q ⟧)
v ⟦ p ∨ q ⟧ = (v ⟦ p ⟧) or  (v ⟦ q ⟧)
v ⟦ p ⊃ q ⟧ = (v ⟦ p ⟧) imp (v ⟦ q ⟧)
v ⟦ ¬ p ⟧ = not (v ⟦ p ⟧)
--v ⟦ ⊤  ⟧ = t
--v ⟦ ⊥ ⟧ = f

open import Relation.Binary.PropositionalEquality 
  renaming (_≡_ to _≈_) --hiding ([_]) 
open import Relation.Nullary using (yes;no;Dec)

-- 論理式がトートロジーであることの定義は p.7 にあるが，本コードでは教科書の様にはトートロジーを定義していない．
isTautology : PropForm → Set
isTautology A = (v : Assign) → v ⟦ A ⟧ ≈ t

-- p.7
-- 与えられた論理式がトートロジーかどうかを判定することは決定可能である
-- (トートロジーかどうかを判定する有限の手続きが存在する)
theorem1-1 : (v : Assign) (A : PropForm) → Dec (v ⟦ A ⟧ ≈ t)
theorem1-1 v (var x) with v ⟦ var x ⟧
theorem1-1 v (var x) | t = yes refl
theorem1-1 v (var x) | f = no (λ ())
theorem1-1 v (A ∧ B) with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-1 v (A ∧ B) | t | t = yes refl
theorem1-1 v (A ∧ B) | t | f = no (λ ())
theorem1-1 v (A ∧ B) | f | _ = no (λ ())
theorem1-1 v (A ∨ B) with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-1 v (A ∨ B) | t | _ = yes refl
theorem1-1 v (A ∨ B) | f | t = yes refl
theorem1-1 v (A ∨ B) | f | f = no (λ ())
theorem1-1 v (A ⊃ B) with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-1 v (A ⊃ B) | t | t = yes refl
theorem1-1 v (A ⊃ B) | t | f = no (λ ())
theorem1-1 v (A ⊃ B) | f | _ = yes refl
theorem1-1 v (¬ A) with v ⟦ A ⟧
theorem1-1 v (¬ A) | t = no (λ ())
theorem1-1 v (¬ A) | f = yes refl

-- 部分論理式 p.8
postulate
  SubForm : Set

isSatisfiable : PropForm → Set
isSatisfiable A = Σ Assign (λ v → (v ⟦ A ⟧) ≈ t)

-- 充足可能な論理式の例； 0 1 は命題変数である．
R : isSatisfiable (¬ (var Z) ∧ (var (Suc Z)))
R = u , refl
  where
    u : prop → Bool
    u Z       = f
    u (Suc Z) = t
    u _       = t

-- p.10 論理式が充足不可能である (unsatisfiable) の直感的な定義は，どんな付値を与えても論理式が値 f をとることであるので．
-- 下記のように定義できる．教科書の定義と違うので ' をつけている．
isUnsatisfiable' : PropForm → Set
isUnsatisfiable' A = (v : Assign) → v ⟦ A ⟧ ≈ f

open import Relation.Nullary renaming ( ¬_ to Not_) 

-- ~でない Relation.Nullary.Core の ¬ と論理式の ¬ がかぶるので Not という記号を用いる


-- p.10 論理式が充足不可能である (unsatisfiable) の教科書の定義
isUnsatisfiable : PropForm → Set
isUnsatisfiable A = Not isSatisfiable A

-- 充足不可能に関して教科書の定義と自分の直感的な定義が等しいことの証明
-- isUnsatisfiable ⇔ isUnsatisfiable' を示す．
-- その為に， isUnsatisfiable' A → isUnsatisfiable A と isUnsatisfiable A → isUnsatisfiable' A を示す．

open import Data.Empty 
open import Relation.Nullary.Negation 

isUnsatisfiable'⇒isUnsatisfiable : {A : PropForm} → isUnsatisfiable' A → isUnsatisfiable A
isUnsatisfiable'⇒isUnsatisfiable {A} prf (u , prf2) = lemma {u} {A} prf2 (prf u)
  where
   lemma : ∀ {u A} → u ⟦ A ⟧ ≈ t → u ⟦ A ⟧ ≈ f → ⊥
   lemma {u} {A}  prf1 prf2 with u ⟦ A ⟧
   lemma prf2 () | t
   lemma () prf2 | f


isUnsatisfiable⇒isUnsatisfiable' : {A : PropForm} → isUnsatisfiable A → isUnsatisfiable' A
isUnsatisfiable⇒isUnsatisfiable' {A} prf u with u ⟦ A ⟧ | inspect (_⟦_⟧ u) A 
isUnsatisfiable⇒isUnsatisfiable' prf u | t | [ eq ] = contradiction (u , eq) prf
isUnsatisfiable⇒isUnsatisfiable' prf u | f | _ = refl


-- p.10 定理1.2 論理式Aが充足不可能であるための必要十分条件は¬Aがトートロジーとなることである． 
-- theorem1-2 : (v : Assign) → (A : PropForm) → (isUnsatisfiable A ⇔ isTautology (PropForm.¬_ A))
-- theorem1-2 v A = {!!}

theorem1-2' : (A : PropForm) → (isUnsatisfiable A → isTautology (PropForm.¬_ A))
theorem1-2' A prf v with v ⟦ A ⟧ | inspect (_⟦_⟧ v) A
theorem1-2' A prf v | t | [ eq ] = contradiction (v , eq) prf
theorem1-2' A prf v | f | [ eq ] = refl

theorem1-2'' : (A : PropForm) → (isTautology (PropForm.¬_ A) → isUnsatisfiable A)
theorem1-2'' A prf1 (v , prf2) with v ⟦ A ⟧ | inspect (_⟦_⟧ v) A
theorem1-2'' A prf1 (v , refl) | t | [ eq ] = lemma {v} {A} eq (prf1 v)
  where
   lemma : ∀ {u A} → u ⟦ A ⟧ ≈ t → not (u ⟦ A ⟧) ≈ t → ⊥
   lemma {u} {A}  prf1 prf2 with u ⟦ A ⟧
   lemma _ () | t
   lemma () _ | f
theorem1-2'' A prf1 (v , ()) | f | [ eq ]

-- p.10 問1.1
-- 1) A ⊃ B および A がともに充足可能ならば，B も充足可能である．
-- 1) の命題は正しくないので，1) の否定
e1-1-1 : Not (∀ A B → isSatisfiable (A ⊃ B) → isSatisfiable A → isSatisfiable B)
-- を示す．
e1-1-1 = lemma⇒e1-1-1 lemma
  where
    lemma : ∃ (λ A → ∃ (λ B → Not (isSatisfiable (A ⊃ B) → isSatisfiable A → isSatisfiable B)))
    lemma = var Z , (var (Suc Z) ∧ ¬ var (Suc Z) , 
            (λ assumption → contradiction' {var (Suc Z) ∧ ¬ var (Suc Z)} (assumption prf1 prf2) prf3))
      where
        prf1 : isSatisfiable (var Z ⊃ var (Suc Z) ∧ ¬ var (Suc Z))
        prf1 = (λ x → f) , refl
        prf2 : isSatisfiable (var Z)
        prf2 = (λ x → t) , refl
        prf3 : isUnsatisfiable (var (Suc Z) ∧ ¬ var (Suc Z))
        prf3 (v , prf) with v ⟦ var (Suc Z) ⟧
        prf3 (v , ()) | t
        prf3 (v , ()) | f

        contradiction' : ∀ {A} → isSatisfiable A → isUnsatisfiable A → ⊥
        contradiction' sat unsat = unsat sat

    -- lemmaならばe1-1-1であることの証明。
    lemma⇒e1-1-1 : 
             ∃ (λ A → ∃ (λ B → Not (isSatisfiable (A ⊃ B) → isSatisfiable A → isSatisfiable B)))
          →  Not (∀ A B → isSatisfiable (A ⊃ B) → isSatisfiable A → isSatisfiable B)
    lemma⇒e1-1-1 (a , b , prf) = ∃¬⟶¬∀ (a , ∃¬⟶¬∀ (b , prf))

-- 2) A ⊃ B がトートロジーで A が充足可能ならば，B も充足可能である．

open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function

lemma1 : ∀ b → {X : Set} → b ≈ t → b ≈ f → X
lemma1 t _  ()
lemma1 f () _

-- 2) A ⊃ B がトートロジーで A が充足可能ならば，B も充足可能である．
-- 直観的に解かり易いと思われる証明
e1-1-2' : ∀ A B → isTautology (A ⊃ B) → isSatisfiable A → isSatisfiable B
e1-1-2' A B prf1 (v , prf2) with v ⟦ A ⟧ | v ⟦ B ⟧ | inspect (_⟦_⟧ v) A | inspect (_⟦_⟧ v) B
e1-1-2' A B prf1 (v , prf2) | t | t | _ | [ eq ] = v , eq
e1-1-2' A B prf1 (v , prf2) | t | f | [ eq ] | [ eq' ] = lemma (sym
  (begin
    f
    ≡⟨ refl ⟩
    t imp f
    ≡⟨ cong₂ (λ x y → x imp y) (sym eq) (sym eq') ⟩
    (v ⟦ A ⟧) imp (v ⟦ B ⟧)
    ≡⟨ prf1 v ⟩
    (t ∎)))
      where
        lemma : {X : Set} → t ≈ f → X
        lemma ()
e1-1-2' A B prf1 (v , ()) | f | _ | _ | _

-- 簡潔な証明
e1-1-2'' : ∀ A B → isTautology (A ⊃ B) → isSatisfiable A → isSatisfiable B
e1-1-2'' A B prf1 (v , prf2) with v ⟦ A ⟧ | v ⟦ B ⟧ | inspect (_⟦_⟧ v) A | inspect (_⟦_⟧ v) B
e1-1-2'' A B prf1 (v , prf2) | t | t | _      | [ eq ] = v , eq
e1-1-2'' A B prf1 (v , prf2) | t | f | [ eq ] | [ eq' ] = lemma ((v ⟦ A ⟧) imp (v ⟦ B ⟧)) (prf1 v) (cong₂ _imp_ eq eq')
  where
    lemma : ∀ b → {X : Set} → b ≈ t → b ≈ f → X
    lemma t _  ()
    lemma f () _
e1-1-2'' A B prf1 (v , ()) | f | _ | _ | _

-- 原田が最初に書いた下品かつ解かり難い証明
e1-1-2 : ∀ A B → isTautology (A ⊃ B) → isSatisfiable A → isSatisfiable B
e1-1-2 A B prf1 (v , prf2) with v ⟦ A ⟧ | v ⟦ B ⟧ | inspect (_⟦_⟧ v) A | inspect (_⟦_⟧ v) B
e1-1-2 A B prf1 (v , prf2) | t | t | _ | [ eq ] = v , eq
e1-1-2 A B prf1 (v , prf2) | t | f | [ eq ] | [ eq2 ] = contradiction (lemmaP v A B eq (prf1 v)) (lemmaQ v B eq2)
  where
    lemmaP : (v : Assign) → (A : PropForm) → (B : PropForm) → v ⟦ A ⟧ ≈ t → (v ⟦ A ⟧) imp (v ⟦ B ⟧) ≈ t → v ⟦ B ⟧ ≈ t
    lemmaP v A B prf1 prf2 with v ⟦ A ⟧ | v ⟦ B ⟧
    lemmaP v A B prf1 prf2 | t | t = refl
    lemmaP v A B prf1 ()   | t | f
    lemmaP v A B prf1 prf2 | f | t = refl
    lemmaP v A B ()   prf2 | f | f
    lemmaQ : (v : Assign) → (B : PropForm) → v ⟦ B ⟧ ≈ f → Not (v ⟦ B ⟧ ≈ t)
    lemmaQ v B prf1 = λ x → lemma {v} {B} x prf1
      where
        lemma : ∀ {u A} → u ⟦ A ⟧ ≈ t → u ⟦ A ⟧ ≈ f → ⊥
        lemma {u} {A}  prf1 prf2 with u ⟦ A ⟧
        lemma prf2 () | t
        lemma () prf2 | f
e1-1-2 A B prf1 (v , ()) | f | _ | _ | _

-- p.10 問1.2 ((p ∨ q) ⊃ r) ∨ (p ∧ q) の値を f にするには，p,q,r にどのような値の組を与えればよいか．このような値の組をすべて求めよ．
e1-2 : ∀ v p q r → (Dec (v ⟦ (((p ∨ q) ⊃ r) ∨ (p ∧ q)) ⟧ ≈ f))
e1-2 v p q r with v ⟦ p ⟧ | v ⟦ q ⟧ | v ⟦ r ⟧
e1-2 v p q r | t | t | t = no (λ ())
e1-2 v p q r | t | t | f = no (λ ())
e1-2 v p q r | t | f | t = no (λ ())
e1-2 v p q r | t | f | f = yes refl   -- ((t ∨ f) ⊃ f) ∨ (t ∧ f) = f
e1-2 v p q r | f | t | t = no (λ ())
e1-2 v p q r | f | t | f = yes refl   -- ((f ∨ t) ⊃ f) ∨ (f ∧ t) = f
e1-2 v p q r | f | f | t = no (λ ())
e1-2 v p q r | f | f | f = no (λ ())

-- p.10 問1.3 論理結合子として ⊃ と ∧ のみを含むような論理式はすべて充足可能であることを示せ．
containOnly⊃And∧ : PropForm → Bool
containOnly⊃And∧ (var x) = t
containOnly⊃And∧ (A ∧ B) = containOnly⊃And∧ A and containOnly⊃And∧ B
containOnly⊃And∧ (_ ∨ _) = f
containOnly⊃And∧ (A ⊃ B) = containOnly⊃And∧ A and containOnly⊃And∧ B
containOnly⊃And∧ (¬ A) = f

ContainOnly⊃And∧ : PropForm → Set
ContainOnly⊃And∧ A = containOnly⊃And∧ A ≈ t

_isSatisfiableBy_ : PropForm → Assign → Set
A isSatisfiableBy v = v ⟦ A ⟧ ≈ t

PropFormElim1 : (A B : PropForm) → containOnly⊃And∧ (A ∧ B) ≈ t → containOnly⊃And∧ A ≈ t
PropFormElim1 A B prf with containOnly⊃And∧ A | containOnly⊃And∧ B
PropFormElim1 A B prf | t | _ = refl
PropFormElim1 A B ()  | f | _

PropFormElim2 : (A B : PropForm) → containOnly⊃And∧ (A ∧ B) ≈ t → containOnly⊃And∧ B ≈ t
PropFormElim2 A B prf with containOnly⊃And∧ A | containOnly⊃And∧ B
PropFormElim2 A B prf | _ | t = refl
PropFormElim2 A B ()  | t | f
PropFormElim2 A B ()  | f | f

e1-1-3' : (A : PropForm) → containOnly⊃And∧ A ≈ t → A isSatisfiableBy (λ x → t)
e1-1-3' (var x) prf = refl
e1-1-3' (A ∧ B) prf rewrite e1-1-3' A (PropFormElim1 A B prf) | e1-1-3' B (PropFormElim2 A B prf) = refl
e1-1-3' (A ∨ B) ()
-- rewriteは以下のwithのsyntax sugar.
e1-1-3' (A ⊃ B) prf with (λ x → t) ⟦ A ⟧ | e1-1-3' A (PropFormElim1 A B prf) | (λ x → t) ⟦ B ⟧ | e1-1-3' B (PropFormElim2 A B prf)
... | ._ | refl | ._ | refl = refl
e1-1-3' (¬ A) ()

-- e1-1-3 : (A : PropForm) → containOnly⊃And∧ A → isSatisfiable A
-- e1-1-3 (var x) prf = (λ A → t) , refl
-- e1-1-3 (A ∧ B) prf = {!!}
-- e1-1-3 (A ∨ B) ()
-- e1-1-3 (A ⊃ B) prf with isContainOnly⊃And∧ A | isContainOnly⊃And∧ B | inspect isContainOnly⊃And∧ A | inspect isContainOnly⊃And∧ B
-- e1-1-3 (A ⊃ B) prf | t | t | [ eqA ] | [ eqB ] = lemma A B (e1-1-3 A eqA) (e1-1-3 B eqB)
--   where
--     lemma : ∀ A B → isSatisfiable A → isSatisfiable B → isSatisfiable (A ⊃ B)
--     lemma A B prfA prfB = {!!}
-- e1-1-3 (A ⊃ B) ()  | t | f | _ | _
-- e1-1-3 (A ⊃ B) ()  | f | t | _ | _
-- e1-1-3 (A ⊃ B) ()  | f | f | _ | _
-- e1-1-3 (¬ _) ()

infix 1 _≡_
_≡_ : PropForm → PropForm → PropForm
A ≡ B = (A ⊃ B) ∧ (B ⊃ A)

-- 問1.4 v(A ≡ B) = t ⇔ v(A) = v(B)
e1-1-4 : {v : Assign} {A B : PropForm} → (v ⟦ (A ≡ B) ⟧ ≈ t) ⇔ (v ⟦ A ⟧ ≈ v ⟦ B ⟧)
e1-1-4 {v} {A} {B} with v ⟦ A ⟧ | v ⟦ B ⟧
e1-1-4 | t | t = (λ _ → refl) , (λ _ → refl)
e1-1-4 | t | f = (λ ()) , (λ ())
e1-1-4 | f | t = (λ ()) , (λ ())
e1-1-4 | f | f = (λ _ → refl) , (λ _ → refl)

-- p.11 問1.5 v(A ≡ B) ≈ v((A ∧ B) ∨ (¬ A ∧ B))
e1-1-5 : {v : Assign} {A B : PropForm} → v ⟦ A ≡ B ⟧ ≈ (v ⟦ (A ∧ B) ∨ (¬ A ∧ ¬ B) ⟧)
e1-1-5 {v} {A} {B} with v ⟦ A ⟧ | v ⟦ B ⟧
e1-1-5 | t | t = refl
e1-1-5 | t | f = refl
e1-1-5 | f | t = refl
e1-1-5 | f | f = refl

-- 定理1.3 次の論理式はそれぞれトートロジーである．
theorem1-3-1-1 : {A : PropForm} → isTautology (A ∧ A ≡ A)  -- 冪等律
theorem1-3-1-1 {A} v with v ⟦ A ⟧
theorem1-3-1-1 v | t = refl
theorem1-3-1-1 v | f = refl

theorem1-3-1-2 : {A : PropForm} → isTautology (A ∨ A ≡ A)  -- 冪等律
theorem1-3-1-2 {A} v with v ⟦ A ⟧
theorem1-3-1-2 v | t = refl
theorem1-3-1-2 v | f = refl

theorem1-3-2-1 : {A B C : PropForm} → isTautology ((A ∧ (B ∧ C)) ≡ ((A ∧ B) ∧ C))  -- 結合律
theorem1-3-2-1 {A} {B} {C} v with v ⟦ A ⟧ | v ⟦ B ⟧ | v ⟦ C ⟧
theorem1-3-2-1 v | t | t | t = refl
theorem1-3-2-1 v | t | f | t = refl
theorem1-3-2-1 v | t | t | f = refl
theorem1-3-2-1 v | t | f | f = refl
theorem1-3-2-1 v | f | _ | _ = refl

theorem1-3-2-2 : {A B C : PropForm} → isTautology ((A ∨ (B ∨ C)) ≡ ((A ∨ B) ∨ C))  -- 結合律
theorem1-3-2-2 {A} {B} {C} v with v ⟦ A ⟧ | v ⟦ B ⟧ | v ⟦ C ⟧
theorem1-3-2-2 v | t | _ | _ = refl
theorem1-3-2-2 v | f | t | _ = refl
theorem1-3-2-2 v | f | f | t = refl
theorem1-3-2-2 v | f | f | f = refl

theorem1-3-3-1 : {A B : PropForm} → isTautology ((A ∧ B) ≡ (B ∧ A))  -- 交換律
theorem1-3-3-1 {A} {B} v with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-3-3-1 v | t | t = refl
theorem1-3-3-1 v | t | f = refl
theorem1-3-3-1 v | f | t = refl
theorem1-3-3-1 v | f | f = refl

theorem1-3-3-2 : {A B : PropForm} → isTautology ((A ∨ B) ≡ (B ∨ A))  -- 交換律
theorem1-3-3-2 {A} {B} v with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-3-3-2 v | t | t = refl
theorem1-3-3-2 v | t | f = refl
theorem1-3-3-2 v | f | t = refl
theorem1-3-3-2 v | f | f = refl

theorem1-3-4-1 : {A B : PropForm} → isTautology ((A ∧ (A ∨ B)) ≡ A)  -- 吸収律
theorem1-3-4-1 {A} v with v ⟦ A ⟧ 
theorem1-3-4-1 v | t = refl
theorem1-3-4-1 v | f = refl

theorem1-3-4-2 : {A B : PropForm} → isTautology ((A ∨ (A ∧ B)) ≡ A)  -- 吸収律
theorem1-3-4-2 {A} v with v ⟦ A ⟧ 
theorem1-3-4-2 v | t = refl
theorem1-3-4-2 v | f = refl

theorem1-3-5-1 : {A B C : PropForm} → isTautology ((A ∨ (B ∧ C)) ≡ ((A ∨ B) ∧ (A ∨ C)))  -- 分配律
theorem1-3-5-1 {A} {B} {C} v with v ⟦ A ⟧ | v ⟦ B ⟧ | v ⟦ C ⟧
theorem1-3-5-1 v | t | t | t = refl
theorem1-3-5-1 v | t | t | f = refl
theorem1-3-5-1 v | t | f | t = refl
theorem1-3-5-1 v | t | f | f = refl
theorem1-3-5-1 v | f | t | t = refl
theorem1-3-5-1 v | f | t | f = refl
theorem1-3-5-1 v | f | f | t = refl
theorem1-3-5-1 v | f | f | f = refl

theorem1-3-5-2 : {A B C : PropForm} → isTautology ((A ∧ (B ∨ C)) ≡ ((A ∧ B) ∨ (A ∧ C)))  -- 分配律
theorem1-3-5-2 {A} {B} {C} v with v ⟦ A ⟧ | v ⟦ B ⟧ | v ⟦ C ⟧
theorem1-3-5-2 v | t | t | t = refl
theorem1-3-5-2 v | t | t | f = refl
theorem1-3-5-2 v | t | f | t = refl
theorem1-3-5-2 v | t | f | f = refl
theorem1-3-5-2 v | f | t | t = refl
theorem1-3-5-2 v | f | t | f = refl
theorem1-3-5-2 v | f | f | t = refl
theorem1-3-5-2 v | f | f | f = refl

theorem1-3-6 :  {A : PropForm} → isTautology (¬ ¬ A ≡ A)
theorem1-3-6 {A} v with v ⟦ A ⟧
theorem1-3-6 v | t = refl
theorem1-3-6 v | f = refl

theorem1-3-7-1 : {A B : PropForm} → isTautology ((¬ (A ∨ B)) ≡ (¬ A ∧ ¬ B))  -- De Morgan's Law
theorem1-3-7-1 {A} {B} v with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-3-7-1 v | t | t = refl
theorem1-3-7-1 v | t | f = refl
theorem1-3-7-1 v | f | t = refl
theorem1-3-7-1 v | f | f = refl

theorem1-3-7-2 : {A B : PropForm} → isTautology ((¬ (A ∧ B)) ≡ (¬ A ∨ ¬ B))  -- De Morgan's Law
theorem1-3-7-2 {A} {B} v with v ⟦ A ⟧ | v ⟦ B ⟧
theorem1-3-7-2 v | t | t = refl
theorem1-3-7-2 v | t | f = refl
theorem1-3-7-2 v | f | t = refl
theorem1-3-7-2 v | f | f = refl

-- p.11 問1.6 2) つぎの論理式はトートロジーか．
e1-6-2-1 : {A B C : PropForm} → isTautology ((A ⊃ (B ⊃ C)) ≡ ((A ∧ B) ⊃ C))
e1-6-2-1 {A} {B} {C} v with v ⟦ A ⟧ | v ⟦ B ⟧ | v ⟦ C ⟧
e1-6-2-1 v | t | t | t = refl
e1-6-2-1 v | t | t | f = refl
e1-6-2-1 v | t | f | t = refl
e1-6-2-1 v | t | f | f = refl
e1-6-2-1 v | f | t | _ = refl
e1-6-2-1 v | f | f | _ = refl

-- (¬ (¬ A ⊃ A))) は Tautology ではないので，その否定命題を示す．
{--
e1-6-2-2 : {A : PropForm} → Not (isTautology (¬ (¬ A ⊃ A)))
e1-6-2-2 {A} = lemma⇒e1-6-2-2 {A} (lemma {A})
   where
     lemma : {A : PropForm} → Σ Assign (λ v → (v ⟦ ¬ (¬ A ⊃ A ) ⟧ ≈ f))
     lemma {var x} = (λ y → t) , refl
     lemma {A ∧ B} with (λ x → t) ⟦ A ⟧ | e1-6-2-2 {A} | (λ x → t) ⟦ B ⟧ | e1-6-2-2 {B}
     lemma {A ∧ B} | t | b | t | d = (λ x → t) , {!!}
     lemma {A ∧ B} | t | b | f | d = {!!}
     lemma {A ∧ B} | f | b | c | d = {!!}
     lemma {A ∨ B} = {!!}
     lemma {A ⊃ B} = {!!}
     lemma {¬ A} = {!!}

     lemma⇒e1-6-2-2 : {A : PropForm} → Σ Assign (λ v → (v ⟦ ¬ (¬ A ⊃ A) ⟧ ≈ f)) → Not (isTautology (¬ (¬ A ⊃ A)))
     lemma⇒e1-6-2-2 {A} (u , prfF) = ∃¬⟶¬∀ (u , (λ prfT → lemma2 u A prfT prfF)) 
       where
         lemma2 : (u : Assign) → (A : PropForm) → not (not (u ⟦ A ⟧) imp (u ⟦ A ⟧)) ≈ t → not (not (u ⟦ A ⟧) imp (u ⟦ A ⟧)) ≈ f → ⊥
         lemma2 u A prfT prfF with u ⟦ A ⟧
         lemma2 u A () _  | t
         lemma2 u A _  () | f
--}

{--
e1-1-3' : (A : PropForm) → containOnly⊃And∧ A ≈ t → A isSatisfiableBy (λ x → t)
e1-1-3' (var x) prf = refl
e1-1-3' (A ∧ B) prf rewrite e1-1-3' A (PropFormElim1 A B prf) | e1-1-3' B (PropFormElim2 A B prf) = refl
e1-1-3' (A ∨ B) ()
-- rewriteは以下のwithのsyntax sugar.
e1-1-3' (A ⊃ B) prf with (λ x → t) ⟦ A ⟧ | e1-1-3' A (PropFormElim1 A B prf) | (λ x → t) ⟦ B ⟧ | e1-1-3' B (PropFormElim2 A B prf)
... | ._ | refl | ._ | refl = refl
e1-1-3' (¬ A) ()
--}

e1-6-2-2'' : {x : prop} → Not (isTautology (¬ (¬ (var x) ⊃ (var x))))
e1-6-2-2'' {x} prf = lemma (prf (λ z → t))
  where
    lemma : f ≈ t → ⊥
    lemma ()

e1-6-2-3 : {A : PropForm} → isTautology ((A ⊃ ¬ A) ⊃ ¬ A)
e1-6-2-3 {A} v with v ⟦ A ⟧
e1-6-2-3 v | t = refl
e1-6-2-3 v | f = refl

-- p.12 命題論理式に定数 ⊤, ⊥ をつけ加える．
data Form : Set where
  var : prop → Form         -- 命題変数自体は論理式
  _∧_ : Form → Form → Form
  _∨_ : Form → Form → Form
  _⊃_ : Form → Form → Form
  ¬_  : Form → Form
  ⊤   : Form
  ⊥₂  : Form                -- Data.Empty で ⊥ を使用しているので苦肉の策

-- 付値の拡張
_⟦_⟧₂ : Assign → Form → Bool
v ⟦ var p ⟧₂ = v p
v ⟦ p ∧ q ⟧₂ = (v ⟦ p ⟧₂) and (v ⟦ q ⟧₂)
v ⟦ p ∨ q ⟧₂ = (v ⟦ p ⟧₂) or  (v ⟦ q ⟧₂)
v ⟦ p ⊃ q ⟧₂ = (v ⟦ p ⟧₂) imp (v ⟦ q ⟧₂)
v ⟦ ¬ p ⟧₂ = not (v ⟦ p ⟧₂)
v ⟦ ⊤ ⟧₂ = t
v ⟦ ⊥₂ ⟧₂ = f

-- _≡_ の拡張
infix 1 _≡₂_ 
_≡₂_ : Form → Form → Form
A ≡₂ B = (A ⊃ B) ∧ (B ⊃ A)

-- isTautology の拡張
isTautology' : Form → Set
isTautology' A = (v : Assign) → v ⟦ A ⟧₂ ≈ t

-- 定理1.3 の拡張
theorem1-3-9-1 : {A : Form} → isTautology' ((A ∧ ¬ A) ≡₂ ⊥₂)
theorem1-3-9-1 {A} v with v ⟦ A ⟧₂
theorem1-3-9-1 v | t = refl
theorem1-3-9-1 v | f = refl

theorem1-3-9-2 : {A : Form} → isTautology' ((A ∨ ¬ A) ≡₂ ⊤)
theorem1-3-9-2 {A} v with v ⟦ A ⟧₂
theorem1-3-9-2 v | t = refl
theorem1-3-9-2 v | f = refl

theorem1-3-10-1 : {A : Form} → isTautology' ((A ∨ ⊥₂) ≡₂ A)
theorem1-3-10-1 {A} v with v ⟦ A ⟧₂
theorem1-3-10-1 v | t = refl
theorem1-3-10-1 v | f = refl

theorem1-3-10-2 : {A : Form} → isTautology' ((A ∨ ⊤) ≡₂ ⊤)
theorem1-3-10-2 {A} v with v ⟦ A ⟧₂
theorem1-3-10-2 v | t = refl
theorem1-3-10-2 v | f = refl

theorem1-3-11-1 : {A : Form} → isTautology' ((A ∧ ⊤) ≡₂ A)
theorem1-3-11-1 {A} v with v ⟦ A ⟧₂
theorem1-3-11-1 v | t = refl
theorem1-3-11-1 v | f = refl

theorem1-3-11-2 : {A : Form} → isTautology' ((A ∧ ⊥₂) ≡₂ ⊥₂)
theorem1-3-11-2 {A} v with v ⟦ A ⟧₂
theorem1-3-11-2 v | t = refl
theorem1-3-11-2 v | f = refl

theorem1-3-12-1 : isTautology' (¬ ⊤ ≡₂ ⊥₂)
theorem1-3-12-1 = λ v → refl

theorem1-3-12-2 : isTautology' (¬ ⊥₂ ≡₂ ⊤)
theorem1-3-12-2 = λ v → refl

theorem1-3-13-1 : {A : Form} → isTautology' (¬ A ≡₂ (A ⊃ ⊥₂))
theorem1-3-13-1 {A} v with v ⟦ A ⟧₂
theorem1-3-13-1 v | t = refl
theorem1-3-13-1 v | f = refl

theorem1-3-13-2 : {A : Form} → isTautology' (A ≡₂ (⊤ ⊃ A))
theorem1-3-13-2 {A} v with v ⟦ A ⟧₂
theorem1-3-13-2 v | t = refl
theorem1-3-13-2 v | f = refl

-- p.13 論理的同値性
_~_ : Form → Form → Set
A ~ B = isTautology' (A ≡₂ B)

-- p.13 定理1.4 論理的同値性 ~ についてつぎのことがなりたつ．
theorem1-4-1 : {A : Form} → (A ~ A)
theorem1-4-1 {A} v with v ⟦ A ⟧₂
theorem1-4-1 v | t = refl
theorem1-4-1 v | f = refl

theorem1-4-2 : {A B : Form} → (A ~ B) → (B ~ A)
theorem1-4-2 {A} {B} prf v with v ⟦ A ⟧₂ | v ⟦ B ⟧₂ | inspect (_⟦_⟧₂ v) A | inspect (_⟦_⟧₂ v) B
theorem1-4-2 prf v | t | t | _ | _ = refl
theorem1-4-2 {A} {B} prf v | t | f | [ eq ] | [ eq' ] 
  = lemma1 (((v ⟦ A ⟧₂) imp (v ⟦ B ⟧₂)) and ((v ⟦ B ⟧₂) imp (v ⟦ A ⟧₂))) (prf v) (cong₂ _and_ (cong₂ _imp_ eq eq') (cong₂ _imp_ eq' eq))
theorem1-4-2 {A} {B} prf v | f | t | [ eq ] | [ eq' ]
  = lemma1 (((v ⟦ A ⟧₂) imp (v ⟦ B ⟧₂)) and ((v ⟦ B ⟧₂) imp (v ⟦ A ⟧₂))) (prf v) (cong₂ _and_ (cong₂ _imp_ eq eq') (cong₂ _imp_ eq' eq))
theorem1-4-2 prf v | f | f | _ | _ = refl

theorem1-4-3 : {A B C : Form} → (A ~ B) → (B ~ C) → (A ~ C)
theorem1-4-3 {A} {B} {C} prfAB prfBC v with v ⟦ A ⟧₂ | v ⟦ B ⟧₂ | v ⟦ C ⟧₂ | inspect (_⟦_⟧₂ v) A | inspect (_⟦_⟧₂ v) B | inspect (_⟦_⟧₂ v) C
theorem1-4-3 {A} {B} {C} prfAB prfBC v | t | t | t | [ eqA ] | [ eqB ] | [ eqC ] = refl
theorem1-4-3 {A} {B} {C} prfAB prfBC v | t | t | f | [ eqA ] | [ eqB ] | [ eqC ]
  = lemma1 (((v ⟦ B ⟧₂) imp (v ⟦ C ⟧₂)) and ((v ⟦ C ⟧₂) imp (v ⟦ B ⟧₂))) (prfBC v) (cong₂ _and_ (cong₂ _imp_ eqB eqC) (cong₂ _imp_ eqC eqB))
theorem1-4-3 {A} {B} {C} prfAB prfBC v | t | f | t | [ eqA ] | [ eqB ] | [ eqC ] = refl
theorem1-4-3 {A} {B} {C} prfAB prfBC v | t | f | f | [ eqA ] | [ eqB ] | [ eqC ]
  = lemma1 (((v ⟦ A ⟧₂) imp (v ⟦ B ⟧₂)) and ((v ⟦ B ⟧₂) imp (v ⟦ A ⟧₂))) (prfAB v) (cong₂ _and_ (cong₂ _imp_ eqA eqB) (cong₂ _imp_ eqB eqA))
theorem1-4-3 {A} {B} {C} prfAB prfBC v | f | t | t | [ eqA ] | [ eqB ] | [ eqC ]
  = lemma1 (((v ⟦ A ⟧₂) imp (v ⟦ B ⟧₂)) and ((v ⟦ B ⟧₂) imp (v ⟦ A ⟧₂))) (prfAB v) (cong₂ _and_ (cong₂ _imp_ eqA eqB) (cong₂ _imp_ eqB eqA))
theorem1-4-3 {A} {B} {C} prfAB prfBC v | f | t | f | [ eqA ] | [ eqB ] | [ eqC ] = refl
theorem1-4-3 {A} {B} {C} prfAB prfBC v | f | f | t | [ eqA ] | [ eqB ] | [ eqC ]
  = lemma1 (((v ⟦ B ⟧₂) imp (v ⟦ C ⟧₂)) and ((v ⟦ C ⟧₂) imp (v ⟦ B ⟧₂))) (prfBC v) (cong₂ _and_ (cong₂ _imp_ eqB eqC) (cong₂ _imp_ eqC eqB))
theorem1-4-3 {A} {B} {C} prfAB prfBC v | f | f | f | [ eqA ] | [ eqB ] | [ eqC ] = refl

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

_≟_ : Nat → Nat → Bool
Z ≟ Z = t
Z ≟ Suc n = f
Suc m ≟ Z = f
Suc m ≟ Suc n = m ≟ n

-- 論理式 C の中の命題変数のいくつかの出現を論理式Aでおきかえて得られる論理式を C [ p ≔ A ] と表す（木下修司さんのコードを参考）．

infix 30 _[_≔_]
_[_≔_] : Form → prop → Form → Form
var x [ p ≔ A ] with x ≟ p
var x [ p ≔ A ] | t = A
var x [ p ≔ A ] | f = var x
(C ∧ D) [ p ≔ A ] = C [ p ≔ A ] ∧ D [ p ≔ A ]
(C ∨ D) [ p ≔ A ] = C [ p ≔ A ] ∨ D [ p ≔ A ]
(C ⊃ D) [ p ≔ A ] = C [ p ≔ A ] ⊃ D [ p ≔ A ]
(¬ C) [ p ≔ A ] = ¬ C [ p ≔ A ]
⊤ [ X ≔ Y ] = ⊤
⊥₂ [ X ≔ Y ] = ⊥₂

{--
theorem1-4-4 : (A B C : Form) → (p : prop) → (A ~ B) → C [ p ≔ A ] ~ C [ p ≔ B ]
theorem1-4-4 A B (var x) p prfAB v with x ≟ p
theorem1-4-4 A B (var x) p prfAB v | t = prfAB v
theorem1-4-4 A B (var x) p prfAB v | f = theorem1-4-1 {var x} v
theorem1-4-4 A B (C ∧ D) p prfAB v = {!!}
theorem1-4-4 A B (C ∨ D) p prfAB v = {!!}
theorem1-4-4 A B (C ⊃ D) p prfAB v = {!!}
theorem1-4-4 A B (¬ C) p prfAB v = {!!}
theorem1-4-4 A B ⊤ p prfAB v = refl
theorem1-4-4 A B ⊥₂ p prfAB v = refl
--}

-- p.15 p ⊃ (q ⊃ r) ~ (p ∧ q) ⊃ r が成り立つことを示せ（uncurry）．
e1-8 : (p q r : prop) → (var p ⊃ (var q ⊃ var r)) ~ ((var p ∧ var q) ⊃ var r)
e1-8 p q r v with v ⟦ var p ⟧ | v ⟦ var q ⟧ | v ⟦ var r ⟧
e1-8 p q r v | t | t | t = refl
e1-8 p q r v | t | t | f = refl
e1-8 p q r v | t | f | t = refl
e1-8 p q r v | t | f | f = refl
e1-8 p q r v | f | t | t = refl
e1-8 p q r v | f | t | f = refl
e1-8 p q r v | f | f | t = refl
e1-8 p q r v | f | f | f = refl
