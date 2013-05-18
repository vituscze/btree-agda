open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module BTree
  {a ℓ} {A : Set a} {_<_ : Rel A ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

open import Data.Nat
  using (ℕ; zero; suc)

module Sized where
  open import Relation.Nullary

  open IsStrictTotalOrder isStrictTotalOrder

  -- Add more invariants later.
  data BTree : ℕ → Set a where
    nil : BTree 0
    bt₁ : ∀ {n} (l : BTree n) (x  : A) (r : BTree n) →
          BTree (suc n)
    bt₂ : ∀ {n} (l : BTree n) (x₁ : A) (m : BTree n) (x₂ : A) (r : BTree n) →
          BTree (suc n)

  data Inserted (n : ℕ) : Set a where
    keep : (t : BTree n)                       → Inserted n
    push : (l : BTree n) (x : A) (r : BTree n) → Inserted n

  insert : ∀ {n} → A → BTree n → Inserted n
  insert x nil = push nil x nil

  insert x (bt₁ a b c) with compare x b
  insert x (bt₁ a b c) | tri< _ _ _ with insert x a
  ... | keep a′       = keep (bt₁ a′ b c)
  ... | push a₀ a₁ a₂ = keep (bt₂ a₀ a₁ a₂ b c)
  insert x (bt₁ a b c) | tri≈ _ _ _ = keep (bt₁ a b c)
  insert x (bt₁ a b c) | tri> _ _ _ with insert x c
  ... | keep c′       = keep (bt₁ a b c′)
  ... | push c₀ c₁ c₂ = keep (bt₂ a b c₀ c₁ c₂)

  insert x (bt₂ a b c d e) with compare x b
  insert x (bt₂ a b c d e) | tri< _ _ _ with insert x a
  ... | keep a′       = keep (bt₂ a′ b c d e)
  ... | push a₀ a₁ a₂ = push (bt₁ a₀ a₁ a₂) b (bt₁ c d e)
  insert x (bt₂ a b c d e) | tri≈ _ _ _ = keep (bt₂ a b c d e)
  insert x (bt₂ a b c d e) | tri> _ _ _ with compare x d
  insert x (bt₂ a b c d e) | tri> _ _ _ | tri< _ _ _ with insert x c
  ... | keep c′       = keep (bt₂ a b c′ d e)
  ... | push c₀ c₁ c₂ = push (bt₁ a b c₀) c₁ (bt₁ c₂ d e)
  insert x (bt₂ a b c d e) | tri> _ _ _ | tri≈ _ _ _ = keep (bt₂ a b c d e)
  insert x (bt₂ a b c d e) | tri> _ _ _ | tri> _ _ _ with insert x e
  ... | keep e′       = keep (bt₂ a b c d e′)
  ... | push e₀ e₁ e₂ = push (bt₁ a b c) d (bt₁ e₀ e₁ e₂)

data Tree : Set a where
  some : ∀ {n} → Sized.BTree n → Tree

private
  repack : ∀ {n} → Sized.Inserted n → Tree
  repack (Sized.keep x)     = some x
  repack (Sized.push x l r) = some (Sized.bt₁ x l r)

insert : A → Tree → Tree
insert x (some t) = repack (Sized.insert x t)
