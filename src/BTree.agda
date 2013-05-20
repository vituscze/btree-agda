open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module BTree
  {k v ℓ} {K : Set k} (V : K → Set v)
  {_<_ : Rel K ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

open import Data.Maybe
  using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; zero; suc; _+_)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂)
open import Level
  using (_⊔_)

KV : Set (k ⊔ v)
KV = Σ K V

module Sized where
  open import Relation.Nullary

  open IsStrictTotalOrder isStrictTotalOrder

  data Cmp₂ : Set where
    c< c≈ c> : Cmp₂

  data Cmp₃ : Set where
    c< c≈₁ c>< c≈₂ c> : Cmp₃

  cmp₂ : K → KV → Cmp₂
  cmp₂ a (b , _) with compare a b
  ... | tri< _ _ _ = c<
  ... | tri≈ _ _ _ = c≈
  ... | tri> _ _ _ = c>

  cmp₃ : K → KV → KV → Cmp₃
  cmp₃ a (b , _) (c , _) with compare a b
  ... | tri< _ _ _ = c<
  ... | tri≈ _ _ _ = c≈₁
  ... | tri> _ _ _ with compare a c
  ... | tri< _ _ _ = c><
  ... | tri≈ _ _ _ = c≈₂
  ... | tri> _ _ _ = c>


  -- Add more invariants later.
  data BTree : ℕ → Set (k ⊔ v) where
    nil : BTree 0
    bt₁ : ∀ {n} (l : BTree n) (x  : KV) (r : BTree n) →
          BTree (suc n)
    bt₂ : ∀ {n} (l : BTree n) (x₁ : KV) (m : BTree n) (x₂ : KV) (r : BTree n) →
          BTree (suc n)


  data Inserted (n : ℕ) : Set (k ⊔ v) where
    keep : (t : BTree n)                        → Inserted n
    push : (l : BTree n) (x : KV) (r : BTree n) → Inserted n

  insert : ∀ {n} → (k : K) → V k → BTree n → Inserted n
  insert k v = go
    where
    go : ∀ {n} → BTree n → Inserted n
    go nil = push nil (k , v) nil

    go (bt₁ a b c) with cmp₂ k b
    go (bt₁ a b c) | c< with go a
    ... | keep a′       = keep (bt₁ a′ b c)
    ... | push a₀ a₁ a₂ = keep (bt₂ a₀ a₁ a₂ b c)
    go (bt₁ a b c) | c≈ = keep (bt₁ a (k , v) c)
    go (bt₁ a b c) | c> with go c
    ... | keep c′       = keep (bt₁ a b c′)
    ... | push c₀ c₁ c₂ = keep (bt₂ a b c₀ c₁ c₂)

    go (bt₂ a b c d e) with cmp₃ k b d
    go (bt₂ a b c d e) | c<  with go a
    ... | keep a′       = keep (bt₂ a′ b c d e)
    ... | push a₀ a₁ a₂ = push (bt₁ a₀ a₁ a₂) b (bt₁ c d e)
    go (bt₂ a b c d e) | c≈₁ = keep (bt₂ a (k , v) c d e)
    go (bt₂ a b c d e) | c>< with go c
    ... | keep c′       = keep (bt₂ a b c′ d e)
    ... | push c₀ c₁ c₂ = push (bt₁ a b c₀) c₁ (bt₁ c₂ d e)
    go (bt₂ a b c d e) | c≈₂ = keep (bt₂ a b c (k , v) e)
    go (bt₂ a b c d e) | c>  with go e
    ... | keep e′       = keep (bt₂ a b c d e′)
    ... | push e₀ e₁ e₂ = push (bt₁ a b c) d (bt₁ e₀ e₁ e₂)


  data Deleted : ℕ → Set (k ⊔ v) where
    keep : ∀ {n} (t : BTree n) → Deleted n
    pull : ∀ {n} (t : BTree n) → Deleted (suc n)

  data Replace : ℕ → Set (k ⊔ v) where
    keep : ∀ {n} → KV → BTree n → Replace n
    pull : ∀ {n} → KV → BTree n → Replace (suc n)
    leaf :                        Replace 0

  delete : ∀ {n} → K → BTree n → Deleted n
  delete k = search
    where
    -- Yay, confusing type signatures.
    bt₁₋₁₋₁ : ∀ {n} → BTree n → _
    bt₁₋₁₋₁ a = λ b c d e f g → bt₁ (bt₁ a b c) d (bt₁ e f g)

    bt₁₋₂ˡ : ∀ {n} → BTree n → _
    bt₁₋₂ˡ a = λ b c d e f g → bt₁ (bt₂ a b c d e) f g

    bt₁₋₂ʳ : ∀ {n} → BTree (suc n) → _
    bt₁₋₂ʳ a = λ b c d e f g → bt₁ a b (bt₂ c d e f g)

    bt₂₋₁₋₁ˡ : ∀ {n} → BTree n → _
    bt₂₋₁₋₁ˡ a = λ b c d e f g h i → bt₂ (bt₁ a b c) d (bt₁ e f g) h i

    bt₂₋₁₋₁ʳ : ∀ {n} → BTree (suc n) → _
    bt₂₋₁₋₁ʳ a = λ b c d e f g h i → bt₂ a b (bt₁ c d e) f (bt₁ g h i)


    merge-bt₁-l : ∀ {n} → BTree n → KV → BTree (suc n) → Deleted (2 + n)
    merge-bt₁-l a′ b (bt₁ c₀ c₁ c₂)       = pull (bt₂ a′ b c₀ c₁ c₂)
    merge-bt₁-l a′ b (bt₂ c₀ c₁ c₂ c₃ c₄) = keep (bt₁₋₁₋₁ a′ b c₀ c₁ c₂ c₃ c₄)

    merge-bt₁-r : ∀ {n} → BTree (suc n) → KV → BTree n → Deleted (2 + n)
    merge-bt₁-r (bt₁ a₀ a₁ a₂)       b c′ = pull (bt₂ a₀ a₁ a₂ b c′)
    merge-bt₁-r (bt₂ a₀ a₁ a₂ a₃ a₄) b c′ = keep (bt₁₋₁₋₁ a₀ a₁ a₂ a₃ a₄ b c′)

    merge-bt₂-l : ∀ {n} → BTree n → KV → BTree (suc n) → KV → BTree (suc n) → Deleted (2 + n)
    merge-bt₂-l a′ b (bt₁ c₀ c₁ c₂)       d e = keep (bt₁₋₂ˡ a′ b c₀ c₁ c₂ d e)
    merge-bt₂-l a′ b (bt₂ c₀ c₁ c₂ c₃ c₄) d e = keep (bt₂₋₁₋₁ˡ a′ b c₀ c₁ c₂ c₃ c₄ d e)

    merge-bt₂-m : ∀ {n} → BTree (suc n) → KV → BTree n → KV → BTree (suc n) → Deleted (2 + n)
    merge-bt₂-m a b c′ d (bt₁ e₀ e₁ e₂)       = keep (bt₁₋₂ʳ a b c′ d e₀ e₁ e₂)
    merge-bt₂-m a b c′ d (bt₂ e₀ e₁ e₂ e₃ e₄) = keep (bt₂₋₁₋₁ʳ a b c′ d e₀ e₁ e₂ e₃ e₄)

    merge-bt₂-r : ∀ {n} → BTree (suc n) → KV → BTree (suc n) → KV → BTree n → Deleted (2 + n)
    merge-bt₂-r a b (bt₁ c₀ c₁ c₂)       d e′ = keep (bt₁₋₂ʳ a b c₀ c₁ c₂ d e′)
    merge-bt₂-r a b (bt₂ c₀ c₁ c₂ c₃ c₄) d e′ = keep (bt₂₋₁₋₁ʳ a b c₀ c₁ c₂ c₃ c₄ d e′)


    replace-bt₁-r : ∀ {n} → KV → BTree (suc n) → KV → BTree n → Replace (2 + n)
    replace-bt₁-r k (bt₁ a₀ a₁ a₂)       b c′ = pull k (bt₂ a₀ a₁ a₂ b c′)
    replace-bt₁-r k (bt₂ a₀ a₁ a₂ a₃ a₄) b c′ = keep k (bt₁₋₁₋₁ a₀ a₁ a₂ a₃ a₄ b c′)

    replace-bt₂-r : ∀ {n} → KV → BTree (suc n) → KV → BTree (suc n) → KV → BTree n → Replace (2 + n)
    replace-bt₂-r k a b (bt₁ c₀ c₁ c₂)       d e′ = keep k (bt₁₋₂ʳ a b c₀ c₁ c₂ d e′)
    replace-bt₂-r k a b (bt₂ c₀ c₁ c₂ c₃ c₄) d e′ = keep k (bt₂₋₁₋₁ʳ a b c₀ c₁ c₂ c₃ c₄ d e′)

    replace : ∀ {n} → BTree n → Replace n
    replace nil = leaf
    replace (bt₁ a b c) with replace c
    ... | keep k c′ = keep k (bt₁ a b c′)
    ... | pull k c′ = replace-bt₁-r k a b c′
    ... | leaf      = pull b a
    replace (bt₂ a b c d e) with replace e
    ... | keep k e′ = keep k (bt₂ a b c d e′)
    ... | pull k e′ = replace-bt₂-r k a b c d e′
    ... | leaf      = keep d (bt₁ a b c)


    search : ∀ {n} → BTree n → Deleted n
    search nil = keep nil

    search (bt₁ a b c) with cmp₂ k b
    search (bt₁ a b c) | c< with search a
    ... | keep a′ = keep (bt₁ a′ b c)
    ... | pull a′ = merge-bt₁-l a′ b c
    search (bt₁ a b c) | c≈ with replace a
    ... | keep k a′ = keep (bt₁ a′ k c)
    ... | pull k a′ = merge-bt₁-l a′ k c
    ... | leaf      = pull nil
    search (bt₁ a b c) | c> with search c
    ... | keep c′ = keep (bt₁ a b c′)
    ... | pull c′ = merge-bt₁-r a b c′

    search (bt₂ a b c d e) with cmp₃ k b d
    search (bt₂ a b c d e) | c<  with search a
    ... | keep a′ = keep (bt₂ a′ b c d e)
    ... | pull a′ = merge-bt₂-l a′ b c d e
    search (bt₂ a b c d e) | c≈₁ with replace a
    ... | keep x a′ = keep (bt₂ a′ x c d e)
    ... | pull x a′ = merge-bt₂-l a′ x c d e
    ... | leaf      = keep (bt₁ c d e)
    search (bt₂ a b c d e) | c>< with search c
    ... | keep c′ = keep (bt₂ a b c′ d e)
    ... | pull c′ = merge-bt₂-m a b c′ d e
    search (bt₂ a b c d e) | c≈₂ with replace c
    ... | keep x c′ = keep (bt₂ a b c′ x e)
    ... | pull x c′ = merge-bt₂-m a b c′ x e
    ... | leaf      = keep (bt₁ a b c)
    search (bt₂ a b c d e) | c>  with search e
    ... | keep e′ = keep (bt₂ a b c d e′)
    ... | pull e′ = merge-bt₂-r a b c d e′

  empty : BTree 0
  empty = nil

  singleton : (k : K) → V k → BTree 1
  singleton k v = bt₁ nil (k , v) nil

  lookup : ∀ {n} → (k : K) → BTree n → Maybe (V k)
  lookup k = go
    where
    go : ∀ {n} → BTree n → Maybe (V k)
    go nil = nothing

    -- Alas, can't use cmp₂ nor cmp₃ here. We need the proof that
    -- the keys are indeed equal.
    go (bt₁ a (bk , bv) c) with compare k bk
    ... | tri< _ _ _ = go a
    ... | tri≈ _ p _ rewrite p = just bv
    ... | tri> _ _ _ = go c

    go (bt₂ a (bk , bv) c (dk , dv) e) with compare k bk
    ... | tri< _ _ _ = go a
    ... | tri≈ _ p _ rewrite p = just bv
    ... | tri> _ _ _ with compare k dk
    ... | tri< _ _ _ = go c
    ... | tri≈ _ p _ rewrite p = just dv
    ... | tri> _ _ _ = go e

data Tree : Set (k ⊔ v) where
  some : ∀ {n} → Sized.BTree n → Tree

private
  repack-i : ∀ {n} → Sized.Inserted n → Tree
  repack-i (Sized.keep t)     = some t
  repack-i (Sized.push l x r) = some (Sized.bt₁ l x r)

  repack-d : ∀ {n} → Sized.Deleted n → Tree
  repack-d (Sized.keep t) = some t
  repack-d (Sized.pull t) = some t

insert : (k : K) → V k → Tree → Tree
insert k v (some t) = repack-i (Sized.insert k v t)

delete : K → Tree → Tree
delete k (some t) = repack-d (Sized.delete k t)

empty : Tree
empty = some Sized.empty

singleton : (k : K) → V k → Tree
singleton k v = some (Sized.singleton k v)

lookup : (k : K) → Tree → Maybe (V k)
lookup k (some t) = Sized.lookup k t
