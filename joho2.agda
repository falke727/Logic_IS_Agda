module joho2 where

-- 2章の述語論理を Agda で書きたいが難しいので，始めに言語に用いる各種記号を制限して実装する
-- このコードも木下さんのコード
-- https://github.com/kino3/logic-in-IS/blob/master/PredicateLogic.agda
-- を参考に（ほとんど真似）している.

open import Data.List
open import Data.Nat using (ℕ)

-- p.59
-- 対象変数，対象定数の領域は自然数のみとする．
-- 函数記号は加算 '+' と乗算 '·' と後任函数 'S' の記号のみとする．
-- 述語記号は '≤' と '≡' のみとする．

-- 対象定数 
data OC : Set where
  a b c d : OC

-- 対象変数 
data OV : Set where
  x y z w : OV

-- 函数記号
data F : Set where
  + · S : F

-- 述語記号
data P : Set where
  ≤ ≡ : P

data Term : Set where
  v : OV → Term
  c : OC → Term
  f : F → Term → Term → Term

data AtomicForm : Set where
  f : Term → P → Term → AtomicForm

data PredForm : Set where
  a   : AtomicForm → PredForm
  _∧_ : PredForm → PredForm → PredForm
  _∨_ : PredForm → PredForm → PredForm
  _⊃_ : PredForm → PredForm → PredForm
  ¬_  : PredForm → PredForm
  ALL : OV → PredForm → PredForm
  EX  : OV → PredForm → PredForm

-- 論理式の例 ∀ x (a ≤ x)
example : PredForm
example = ALL x (a (f (c a) ≤ (v x)))
