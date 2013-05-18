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
    merge-bt₁-l : ∀ {n} → BTree n → A → BTree (suc n) → Deleted (2 + n)
    merge-bt₁-l a′ b (bt₁ c₀ c₁ c₂)       = pull (bt₂ a′ b c₀ c₁ c₂)
    merge-bt₁-l a′ b (bt₂ c₀ c₁ c₂ c₃ c₄) = keep (bt₁ (bt₁ a′ b c₀) c₁ (bt₁ c₂ c₃ c₄))

    merge-bt₁-r : ∀ {n} → BTree (suc n) → A → BTree n → Deleted (2 + n)
    merge-bt₁-r (bt₁ a₀ a₁ a₂)       b c′ = pull (bt₂ a₀ a₁ a₂ b c′)
    merge-bt₁-r (bt₂ a₀ a₁ a₂ a₃ a₄) b c′ = keep (bt₁ (bt₁ a₀ a₁ a₂) a₃ (bt₁ a₄ b c′))

    merge-bt₂-l : ∀ {n} → BTree n → A → BTree (suc n) → A → BTree (suc n) → Deleted (2 + n)
    merge-bt₂-l a′ b (bt₁ c₀ c₁ c₂)       d e = keep (bt₁ (bt₂ a′ b c₀ c₁ c₂) d e)
    merge-bt₂-l a′ b (bt₂ c₀ c₁ c₂ c₃ c₄) d e = keep (bt₂ (bt₁ a′ b c₀) c₁ (bt₁ c₂ c₃ c₄) d e)

    merge-bt₂-m : ∀ {n} → BTree (suc n) → A → BTree n → A → BTree (suc n) → Deleted (2 + n)
    merge-bt₂-m a b c′ d (bt₁ e₀ e₁ e₂)       = keep (bt₁ a b (bt₂ c′ d e₀ e₁ e₂))
    merge-bt₂-m a b c′ d (bt₂ e₀ e₁ e₂ e₃ e₄) = keep (bt₂ a b (bt₁ c′ d e₀) e₁ (bt₁ e₂ e₃ e₄))

    merge-bt₂-r : ∀ {n} → BTree (suc n) → A → BTree (suc n) → A → BTree n → Deleted (2 + n)
    merge-bt₂-r a b (bt₁ c₀ c₁ c₂)       d e′ = keep (bt₁ a b (bt₂ c₀ c₁ c₂ d e′))
    merge-bt₂-r a b (bt₂ c₀ c₁ c₂ c₃ c₄) d e′ = keep (bt₂ a b (bt₁ c₀ c₁ c₂) c₃ (bt₁ c₄ d e′))

    data Replace : ℕ → Set a where
      keep : ∀ {n} → A → BTree n → Replace n
      pull : ∀ {n} → A → BTree n → Replace (suc n)
      leaf :                       Replace 0

    replace-bt₁-r : ∀ {n} → A → BTree (suc n) → A → BTree n → Replace (2 + n)
    replace-bt₁-r x (bt₁ a₀ a₁ a₂)       b c′ = pull x (bt₂ a₀ a₁ a₂ b c′)
    replace-bt₁-r x (bt₂ a₀ a₁ a₂ a₃ a₄) b c′ = keep x (bt₁ (bt₁ a₀ a₁ a₂) a₃ (bt₁ a₄ b c′))

    replace-bt₂-r : ∀ {n} → A → BTree (suc n) → A → BTree (suc n) → A → BTree n → Replace (2 + n)
    replace-bt₂-r x a b (bt₁ c₀ c₁ c₂)       d e′ = keep x (bt₁ a b (bt₂ c₀ c₁ c₂ d e′))
    replace-bt₂-r x a b (bt₂ c₀ c₁ c₂ c₃ c₄) d e′ = keep x (bt₂ a b (bt₁ c₀ c₁ c₂) c₃ (bt₁ c₄ d e′))

    replace : ∀ {n} → BTree n → Replace n
    replace nil = leaf
    replace (bt₁ a b c) with replace c
    ... | keep x c′ = keep x (bt₁ a b c′)
    ... | pull x c′ = replace-bt₁-r x a b c′
    ... | leaf      = pull b a
    replace (bt₂ a b c d e) with replace e
    ... | keep x e′ = keep x (bt₂ a b c d e′)
    ... | pull x e′ = replace-bt₂-r x a b c d e′
    ... | leaf      = keep d (bt₁ a b c)

    search : ∀ {n} → BTree n → Deleted n
    search nil = keep nil

    search (bt₁ a b c) with compare x b
    search (bt₁ a b c) | tri< _ _ _ with search a
    ... | keep a′ = keep (bt₁ a′ b c)
    ... | pull a′ = merge-bt₁-l a′ b c
    search (bt₁ a b c) | tri≈ _ _ _ with replace a
    ... | keep x a′ = keep (bt₁ a′ x c)
    ... | pull x a′ = merge-bt₁-l a′ x c
    ... | leaf      = pull nil
    search (bt₁ a b c) | tri> _ _ _ with search c
    ... | keep c′ = keep (bt₁ a b c′)
    ... | pull c′ = merge-bt₁-r a b c′

    search (bt₂ a b c d e) with compare x b
    search (bt₂ a b c d e) | tri< _ _ _ with search a
    ... | keep a′ = keep (bt₂ a′ b c d e)
    ... | pull a′ = merge-bt₂-l a′ b c d e
    search (bt₂ a b c d e) | tri≈ _ _ _ with replace a
    ... | keep x a′ = keep (bt₂ a′ x c d e)
    ... | pull x a′ = merge-bt₂-l a′ x c d e
    ... | leaf      = keep (bt₁ c d e)
    search (bt₂ a b c d e) | tri> _ _ _ with compare x d
    search (bt₂ a b c d e) | tri> _ _ _ | tri< _ _ _ with search c
    ... | keep c′ = keep (bt₂ a b c′ d e)
    ... | pull c′ = merge-bt₂-m a b c′ d e
    search (bt₂ a b c d e) | tri> _ _ _ | tri≈ _ _ _ with replace c
    ... | keep x c′ = keep (bt₂ a b c′ x e)
    ... | pull x c′ = merge-bt₂-m a b c′ x e
    ... | leaf      = keep (bt₁ a b c)
    search (bt₂ a b c d e) | tri> _ _ _ | tri> _ _ _ with search e
    ... | keep e′ = keep (bt₂ a b c d e′)
    ... | pull e′ = merge-bt₂-r a b c d e′

data Tree : Set a where
  some : ∀ {n} → Sized.BTree n → Tree

private
  repack-i : ∀ {n} → Sized.Inserted n → Tree
  repack-i (Sized.keep t)     = some t
  repack-i (Sized.push l x r) = some (Sized.bt₁ l x r)

  repack-d : ∀ {n} → Sized.Deleted n → Tree
  repack-d (Sized.keep t) = some t
  repack-d (Sized.pull t) = some t

insert : A → Tree → Tree
insert x (some t) = repack-i (Sized.insert x t)

delete : A → Tree → Tree
delete x (some t) = repack-d (Sized.delete x t)
