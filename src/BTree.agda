open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module BTree
  {a ℓ} {A : Set a} {_<_ : Rel A ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

open import Data.Nat
  using (ℕ; zero; suc; _+_)

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

  data Deleted : ℕ → Set a where
    keep : ∀ {n} (t : BTree n) → Deleted n
    pull : ∀ {n} (t : BTree n) → Deleted (suc n)

  delete : ∀ {n} → A → BTree n → Deleted n
  delete x = search
    where
    keep₂ : ∀ {n}
            (l : BTree n)  (x₁ : A) (ml : BTree n)
            (x₂ : A)
            (mr : BTree n) (x₃ : A) (l : BTree n) →
            Deleted (2 + n)
    keep₂ a b c d e f g = keep (bt₁ (bt₁ a b c) d (bt₁ e f g))

    search : ∀ {n} → BTree n → Deleted n
    search nil = keep nil

    search (bt₁ a b c) with compare x b
    search (bt₁ a b c) | tri< _ _ _ with search a
    search (bt₁ a b c)                    | tri< _ _ _ | keep a′ = keep (bt₁ a′ b c)
    search (bt₁ a b (bt₁ c₀ c₁ c₂))       | tri< _ _ _ | pull a′ = pull (bt₂ a′ b c₀ c₁ c₂)
    search (bt₁ a b (bt₂ c₀ c₁ c₂ c₃ c₄)) | tri< _ _ _ | pull a′ = keep₂ a′ b c₀ c₁ c₂ c₃ c₄
    search (bt₁ a b c) | tri≈ _ _ _ = {!!}
    search (bt₁ a b c) | tri> _ _ _ with search c
    search (bt₁ a b c)                    | tri> _ _ _ | keep c′ = keep (bt₁ a b c′)
    search (bt₁ (bt₁ a₀ a₁ a₂) b c)       | tri> _ _ _ | pull c′ = pull (bt₂ a₀ a₁ a₂ b c′)
    search (bt₁ (bt₂ a₀ a₁ a₂ a₃ a₄) b c) | tri> _ _ _ | pull c′ = keep₂ a₀ a₁ a₂ a₃ a₄ b c′

    search (bt₂ a b c d e) with compare x b
    search (bt₂ a b c d e) | tri< _ _ _ with search a
    search (bt₂ a b c d e) | tri< _ _ _ | keep a′ = keep (bt₂ a′ b c d e)
    search (bt₂ a b (bt₁ c₀ c₁ c₂) d e)       | tri< _ _ _ | pull a′ = keep (bt₁ (bt₂ a′ b c₀ c₁ c₂) d e)
    search (bt₂ a b (bt₂ c₀ c₁ c₂ c₃ c₄) d e) | tri< _ _ _ | pull a′ = keep (bt₂ (bt₁ a′ b c₀) c₁ (bt₁ c₂ c₃ c₄) d e)
    search (bt₂ a b c d e) | tri≈ _ _ _ = {!!}
    search (bt₂ a b c d e) | tri> _ _ _ with compare x d
    search (bt₂ a b c d e) | tri> _ _ _ | tri< _ _ _ with search c
    search (bt₂ a b c d e) | tri> _ _ _ | tri< _ _ _ | keep c′ = keep (bt₂ a b c′ d e)
    search (bt₂ a b c d (bt₁ e₀ e₁ e₂))       | tri> _ _ _ | tri< _ _ _ | pull c′ = keep (bt₁ a b (bt₂ c′ d e₀ e₁ e₂))
    search (bt₂ a b c d (bt₂ e₀ e₁ e₂ e₃ e₄)) | tri> _ _ _ | tri< _ _ _ | pull c′ = keep (bt₂ a b (bt₁ c′ d e₀) e₁ (bt₁ e₂ e₃ e₄))
    search (bt₂ a b c d e) | tri> _ _ _ | tri≈ _ _ _ = {!!}
    search (bt₂ a b c d e) | tri> _ _ _ | tri> _ _ _ with search e
    search (bt₂ a b c d e) | tri> _ _ _ | tri> _ _ _ | keep e′ = keep (bt₂ a b c d e′)
    search (bt₂ a b (bt₁ c₀ c₁ c₂) d e)       | tri> _ _ _ | tri> _ _ _ | pull e′ = keep (bt₁ a b (bt₂ c₀ c₁ c₂ d e′))
    search (bt₂ a b (bt₂ c₀ c₁ c₂ c₃ c₄) d e) | tri> _ _ _ | tri> _ _ _ | pull e′ = keep (bt₂ a b (bt₁ c₀ c₁ c₂) c₃ (bt₁ c₄ d e′))

data Tree : Set a where
  some : ∀ {n} → Sized.BTree n → Tree

private
  repack : ∀ {n} → Sized.Inserted n → Tree
  repack (Sized.keep t)     = some t
  repack (Sized.push l x r) = some (Sized.bt₁ l x r)

insert : A → Tree → Tree
insert x (some t) = repack (Sized.insert x t)
