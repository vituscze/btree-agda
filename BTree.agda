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
  mutual
    data Node (n : ℕ) : Set a where
      t₁ : (x     : A) (l r   : BTree n) → Node n
      t₂ : (x₁ x₂ : A) (l m r : BTree n) → Node n

    data BTree : ℕ → Set a where
      nil :                  BTree 0
      br  : ∀ {n} → Node n → BTree (suc n)

  data Inserted : ℕ → Set a where
    keep : ∀ {n} → BTree n                 → Inserted n
    push : ∀ {n} → (x : A) (l r : BTree n) → Inserted n

  bt₁ : ∀ {n} → A → BTree n → BTree n → BTree (suc n)
  bt₁ x l r = br (t₁ x l r)

  bt₂ : ∀ {n} → A → A → BTree n → BTree n → BTree n → BTree (suc n)
  bt₂ x₁ x₂ l m r = br (t₂ x₁ x₂ l m r)

  insert : ∀ {n} → A → BTree n → Inserted n
  insert y nil = push y nil nil

  insert y (br (t₁ x l r)) with compare y x
  insert y (br (t₁ x l r)) | tri< _ _ _ with insert y l
  insert y (br (t₁ x l r)) | tri< _ _ _ | keep l′       = keep (bt₁ x l′ r)
  insert y (br (t₁ x l r)) | tri< _ _ _ | push x′ l′ r′ = keep (bt₂ x′ x l′ r′ r)
  insert y (br (t₁ x l r)) | tri≈ _ _ _ = keep (bt₁ x l r)
  insert y (br (t₁ x l r)) | tri> _ _ _ with insert y r
  insert y (br (t₁ x l r)) | tri> _ _ _ | keep r′       = keep (bt₁ x l r′)
  insert y (br (t₁ x l r)) | tri> _ _ _ | push x′ l′ r′ = keep (bt₂ x x′ l l′ r′)

  insert y (br (t₂ x₁ x₂ l m r)) with compare y x₁
  insert y (br (t₂ x₁ x₂ l m r)) | tri< _ _ _ with insert y l
  insert y (br (t₂ x₁ x₂ l m r)) | tri< _ _ _ | keep l′       = keep (bt₂ x₁ x₂ l′ m r)
  insert y (br (t₂ x₁ x₂ l m r)) | tri< _ _ _ | push x′ l′ r′ = push x₁ (bt₁ x′ l′ r′) (bt₁ x₂ m r)
  insert y (br (t₂ x₁ x₂ l m r)) | tri≈ _ _ _ = keep (bt₂ x₁ x₂ l m r)
  insert y (br (t₂ x₁ x₂ l m r)) | tri> _ _ _ with compare y x₂
  insert y (br (t₂ x₁ x₂ l m r)) | tri> _ _ _ | tri< _ _ _ with insert y m
  insert y (br (t₂ x₁ x₂ l m r)) | tri> _ _ _ | tri< _ _ _ | keep m′       = keep (bt₂ x₁ x₂ l m′ r)
  insert y (br (t₂ x₁ x₂ l m r)) | tri> _ _ _ | tri< _ _ _ | push x′ l′ r′ = push x′ (bt₁ x₁ l l′) (bt₁ x₂ r′ r)
  insert y (br (t₂ x₁ x₂ l m r)) | tri> _ _ _ | tri≈ _ _ _ = keep (bt₂ x₁ x₂ l m r)
  insert y (br (t₂ x₁ x₂ l m r)) | tri> _ _ _ | tri> _ _ _ with insert y r
  insert y (br (t₂ x₁ x₂ l m r)) | tri> _ _ _ | tri> _ _ _ | keep r′       = keep (bt₂ x₁ x₂ l m r′)
  insert y (br (t₂ x₁ x₂ l m r)) | tri> _ _ _ | tri> _ _ _ | push x′ l′ r′ = push x₂ (bt₁ x₁ l m) (bt₁ x′ l′ r′)

data Tree : Set a where
  some : ∀ {n} → Sized.BTree n → Tree

private
  repack : ∀ {n} → Sized.Inserted n → Tree
  repack (Sized.keep x)     = some x
  repack (Sized.push x l r) = some (Sized.bt₁ x l r)

insert : A → Tree → Tree
insert x (some t) = repack (Sized.insert x t)
