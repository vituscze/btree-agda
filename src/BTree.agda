open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module BTree
  {k v ℓ} {K : Set k} (V : K → Set v)
  {_<_ : Rel K ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

open import Data.AVL as AVL
  using ()
open import Data.Bool
  using (Bool)
open import Data.DifferenceList as DL
  using (DiffList; []; _∷_; _++_)
open import Data.List
  using (List; foldr)
open import Data.Maybe
  using (Maybe; just; nothing; maybeToBool)
open import Data.Nat
  using (ℕ; zero; suc; _+_)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂; uncurry)
open import Function
  using (_∘_; id; const; flip)
open import Level
  using (_⊔_)

module Extended-key = AVL.Extended-key V isStrictTotalOrder

KV : Set (k ⊔ v)
KV = Σ K V

module Sized where
  open import Relation.Nullary

  open Extended-key
  open IsStrictTotalOrder isStrictTotalOrder

  _>_ = flip _<_

  data Cmp₂ (k₁ k₂ : K) : Set (k ⊔ ℓ) where
    c< : k₁ < k₂ → Cmp₂ k₁ k₂
    c≈ : k₁ ≡ k₂ → Cmp₂ k₁ k₂
    c> : k₁ > k₂ → Cmp₂ k₁ k₂

  data Cmp₃ (k₁ k₂ k₃ : K) : Set (k ⊔ ℓ) where
    c<  : k₁ < k₂ →           Cmp₃ k₁ k₂ k₃
    c≈₁ : k₁ ≡ k₂ →           Cmp₃ k₁ k₂ k₃
    c>< : k₁ > k₂ → k₁ < k₃ → Cmp₃ k₁ k₂ k₃
    c≈₂ : k₁ ≡ k₃ →           Cmp₃ k₁ k₂ k₃
    c>  : k₁ > k₃ →           Cmp₃ k₁ k₂ k₃

  cmp₂ : (k₁ : K) (kv₂ : KV) → Cmp₂ k₁ (proj₁ kv₂)
  cmp₂ a (b , _) with compare a b
  ... | tri< p _ _ = c< p
  ... | tri≈ _ p _ = c≈ p
  ... | tri> _ _ p = c> p

  cmp₃ : (k₁ : K) (kv₂ : KV) (kv₃ : KV) → Cmp₃ k₁ (proj₁ kv₂) (proj₁ kv₃)
  cmp₃ a (b , _) (c , _) with compare a b
  ... | tri< p _ _ = c<  p
  ... | tri≈ _ p _ = c≈₁ p
  ... | tri> _ _ p with compare a c
  ... | tri< q _ _ = c>< p q
  ... | tri≈ _ q _ = c≈₂ q
  ... | tri> _ _ q = c>  q


  data BTree⁺ (lb ub : Key⁺) : ℕ → Set (k ⊔ v ⊔ ℓ) where
    nil : {p : lb <⁺ ub} →
          BTree⁺ lb ub 0
    bt₁ : ∀ {n} (x : KV)
          (l : BTree⁺ lb          [ proj₁ x ] n)
          (r : BTree⁺ [ proj₁ x ] ub          n) →
          BTree⁺ lb ub (suc n)
    bt₂ : ∀ {n} (x₁ x₂ : KV)
          (l : BTree⁺ lb           [ proj₁ x₁ ] n)
          (m : BTree⁺ [ proj₁ x₁ ] [ proj₁ x₂ ] n)
          (r : BTree⁺ [ proj₁ x₂ ] ub           n) →
          BTree⁺ lb ub (suc n)


  data Inserted⁺ (lb ub : Key⁺) (n : ℕ) : Set (k ⊔ v ⊔ ℓ) where
    keep : (t : BTree⁺ lb ub n) →
           Inserted⁺ lb ub n
    push : (x : KV)
           (l : BTree⁺ lb          [ proj₁ x ] n)
           (r : BTree⁺ [ proj₁ x ] ub          n) →
           Inserted⁺ lb ub n

  insertWith⁺ : ∀ {n} (k : K) → V k → (V k → V k → V k) → BTree⁺ ⊥⁺ ⊤⁺ n → Inserted⁺ ⊥⁺ ⊤⁺ n
  insertWith⁺ k v f = go _ _
    where
    go : ∀ {n lb ub} → lb <⁺ [ k ] → [ k ] <⁺ ub → BTree⁺ lb ub n → Inserted⁺ lb ub n
    go p₁ p₂ nil = push (k , v) (nil {p = p₁}) (nil {p = p₂})

    go p₁ p₂ (bt₁ b a c) with cmp₂ k b
    go p₁ p₂ (bt₁ b a c)         | c< pa with go p₁ pa a
    ... | keep a′       = keep (bt₁ b a′ c)
    ... | push a₂ a₁ a₃ = keep (bt₂ a₂ b a₁ a₃ c)
    go p₁ p₂ (bt₁ (bk , bv) a c) | c≈ pb rewrite sym pb = keep (bt₁ (k , f v bv) a c)
    go p₁ p₂ (bt₁ b a c)         | c> pc with go pc p₂ c
    ... | keep c′       = keep (bt₁ b a c′)
    ... | push c₂ c₁ c₃ = keep (bt₂ b c₂ a c₁ c₃)

    go p₁ p₂ (bt₂ b d a c e) with cmp₃ k b d
    go p₁ p₂ (bt₂ b d a c e)         | c<  pa with go p₁ pa a
    ... | keep a′       = keep (bt₂ b d a′ c e)
    ... | push a₂ a₁ a₃ = push b (bt₁ a₂ a₁ a₃) (bt₁ d c e)
    go p₁ p₂ (bt₂ (bk , bv) d a c e) | c≈₁ pb rewrite sym pb = keep (bt₂ (k , f v bv) d a c e)
    go p₁ p₂ (bt₂ b d a c e)         | c>< pc₁ pc₂ with go pc₁ pc₂ c
    ... | keep c′       = keep (bt₂ b d a c′ e)
    ... | push c₂ c₁ c₃ = push c₂ (bt₁ b a c₁) (bt₁ d c₃ e)
    go p₁ p₂ (bt₂ b (dk , dv) a c e) | c≈₂ pd rewrite sym pd = keep (bt₂ b (k , f v dv) a c e)
    go p₁ p₂ (bt₂ b d a c e)         | c>  pe with go pe p₂ e
    ... | keep e′       = keep (bt₂ b d a c e′)
    ... | push e₂ e₁ e₃ = push d (bt₁ b a c) (bt₁ e₂ e₁ e₃)


--   data Deleted : ℕ → Set (k ⊔ v) where
--     keep : ∀ {n} (t : BTree n) → Deleted n
--     pull : ∀ {n} (t : BTree n) → Deleted (suc n)

--   data Replace : ℕ → Set (k ⊔ v) where
--     keep : ∀ {n} → KV → BTree n → Replace n
--     pull : ∀ {n} → KV → BTree n → Replace (suc n)
--     leaf :                        Replace 0

--   delete : ∀ {n} → K → BTree n → Deleted n
--   delete k = search
--     where
--     -- Yay, confusing type signatures.
--     bt₁₋₁₋₁ : ∀ {n} → BTree n → _
--     bt₁₋₁₋₁ a = λ b c d e f g → bt₁ (bt₁ a b c) d (bt₁ e f g)

--     bt₁₋₂ˡ : ∀ {n} → BTree n → _
--     bt₁₋₂ˡ a = λ b c d e f g → bt₁ (bt₂ a b c d e) f g

--     bt₁₋₂ʳ : ∀ {n} → BTree (suc n) → _
--     bt₁₋₂ʳ a = λ b c d e f g → bt₁ a b (bt₂ c d e f g)

--     bt₂₋₁₋₁ˡ : ∀ {n} → BTree n → _
--     bt₂₋₁₋₁ˡ a = λ b c d e f g h i → bt₂ (bt₁ a b c) d (bt₁ e f g) h i

--     bt₂₋₁₋₁ʳ : ∀ {n} → BTree (suc n) → _
--     bt₂₋₁₋₁ʳ a = λ b c d e f g h i → bt₂ a b (bt₁ c d e) f (bt₁ g h i)


--     merge-bt₁-l : ∀ {n} → BTree n → KV → BTree (suc n) → Deleted (2 + n)
--     merge-bt₁-l a′ b (bt₁ c₀ c₁ c₂)       = pull (bt₂ a′ b c₀ c₁ c₂)
--     merge-bt₁-l a′ b (bt₂ c₀ c₁ c₂ c₃ c₄) = keep (bt₁₋₁₋₁ a′ b c₀ c₁ c₂ c₃ c₄)

--     merge-bt₁-r : ∀ {n} → BTree (suc n) → KV → BTree n → Deleted (2 + n)
--     merge-bt₁-r (bt₁ a₀ a₁ a₂)       b c′ = pull (bt₂ a₀ a₁ a₂ b c′)
--     merge-bt₁-r (bt₂ a₀ a₁ a₂ a₃ a₄) b c′ = keep (bt₁₋₁₋₁ a₀ a₁ a₂ a₃ a₄ b c′)

--     merge-bt₂-l : ∀ {n} → BTree n → KV → BTree (suc n) → KV → BTree (suc n) → Deleted (2 + n)
--     merge-bt₂-l a′ b (bt₁ c₀ c₁ c₂)       d e = keep (bt₁₋₂ˡ a′ b c₀ c₁ c₂ d e)
--     merge-bt₂-l a′ b (bt₂ c₀ c₁ c₂ c₃ c₄) d e = keep (bt₂₋₁₋₁ˡ a′ b c₀ c₁ c₂ c₃ c₄ d e)

--     merge-bt₂-m : ∀ {n} → BTree (suc n) → KV → BTree n → KV → BTree (suc n) → Deleted (2 + n)
--     merge-bt₂-m a b c′ d (bt₁ e₀ e₁ e₂)       = keep (bt₁₋₂ʳ a b c′ d e₀ e₁ e₂)
--     merge-bt₂-m a b c′ d (bt₂ e₀ e₁ e₂ e₃ e₄) = keep (bt₂₋₁₋₁ʳ a b c′ d e₀ e₁ e₂ e₃ e₄)

--     merge-bt₂-r : ∀ {n} → BTree (suc n) → KV → BTree (suc n) → KV → BTree n → Deleted (2 + n)
--     merge-bt₂-r a b (bt₁ c₀ c₁ c₂)       d e′ = keep (bt₁₋₂ʳ a b c₀ c₁ c₂ d e′)
--     merge-bt₂-r a b (bt₂ c₀ c₁ c₂ c₃ c₄) d e′ = keep (bt₂₋₁₋₁ʳ a b c₀ c₁ c₂ c₃ c₄ d e′)


--     replace-bt₁-r : ∀ {n} → KV → BTree (suc n) → KV → BTree n → Replace (2 + n)
--     replace-bt₁-r k (bt₁ a₀ a₁ a₂)       b c′ = pull k (bt₂ a₀ a₁ a₂ b c′)
--     replace-bt₁-r k (bt₂ a₀ a₁ a₂ a₃ a₄) b c′ = keep k (bt₁₋₁₋₁ a₀ a₁ a₂ a₃ a₄ b c′)

--     replace-bt₂-r : ∀ {n} → KV → BTree (suc n) → KV → BTree (suc n) → KV → BTree n → Replace (2 + n)
--     replace-bt₂-r k a b (bt₁ c₀ c₁ c₂)       d e′ = keep k (bt₁₋₂ʳ a b c₀ c₁ c₂ d e′)
--     replace-bt₂-r k a b (bt₂ c₀ c₁ c₂ c₃ c₄) d e′ = keep k (bt₂₋₁₋₁ʳ a b c₀ c₁ c₂ c₃ c₄ d e′)

--     replace : ∀ {n} → BTree n → Replace n
--     replace nil = leaf
--     replace (bt₁ a b c) with replace c
--     ... | keep k c′ = keep k (bt₁ a b c′)
--     ... | pull k c′ = replace-bt₁-r k a b c′
--     ... | leaf      = pull b a
--     replace (bt₂ a b c d e) with replace e
--     ... | keep k e′ = keep k (bt₂ a b c d e′)
--     ... | pull k e′ = replace-bt₂-r k a b c d e′
--     ... | leaf      = keep d (bt₁ a b c)


--     search : ∀ {n} → BTree n → Deleted n
--     search nil = keep nil

--     search (bt₁ a b c) with cmp₂ k b
--     search (bt₁ a b c) | c<   with search a
--     ... | keep a′ = keep (bt₁ a′ b c)
--     ... | pull a′ = merge-bt₁-l a′ b c
--     search (bt₁ a b c) | c≈ _ with replace a
--     ... | keep k a′ = keep (bt₁ a′ k c)
--     ... | pull k a′ = merge-bt₁-l a′ k c
--     ... | leaf      = pull nil
--     search (bt₁ a b c) | c>   with search c
--     ... | keep c′ = keep (bt₁ a b c′)
--     ... | pull c′ = merge-bt₁-r a b c′

--     search (bt₂ a b c d e) with cmp₃ k b d
--     search (bt₂ a b c d e) | c<    with search a
--     ... | keep a′ = keep (bt₂ a′ b c d e)
--     ... | pull a′ = merge-bt₂-l a′ b c d e
--     search (bt₂ a b c d e) | c≈₁ _ with replace a
--     ... | keep x a′ = keep (bt₂ a′ x c d e)
--     ... | pull x a′ = merge-bt₂-l a′ x c d e
--     ... | leaf      = keep (bt₁ c d e)
--     search (bt₂ a b c d e) | c><   with search c
--     ... | keep c′ = keep (bt₂ a b c′ d e)
--     ... | pull c′ = merge-bt₂-m a b c′ d e
--     search (bt₂ a b c d e) | c≈₂ _ with replace c
--     ... | keep x c′ = keep (bt₂ a b c′ x e)
--     ... | pull x c′ = merge-bt₂-m a b c′ x e
--     ... | leaf      = keep (bt₁ a b c)
--     search (bt₂ a b c d e) | c>    with search e
--     ... | keep e′ = keep (bt₂ a b c d e′)
--     ... | pull e′ = merge-bt₂-r a b c d e′

--   empty : BTree 0
--   empty = nil

--   singleton : (k : K) → V k → BTree 1
--   singleton k v = bt₁ nil (k , v) nil

--   lookup : ∀ {n} → (k : K) → BTree n → Maybe (V k)
--   lookup k = go
--     where
--     go : ∀ {n} → BTree n → Maybe (V k)
--     go nil = nothing

--     go (bt₁ a b c) with cmp₂ k b
--     ... | c< = go a
--     ... | c≈ p rewrite p = just (proj₂ b)
--     ... | c> = go c

--     go (bt₂ a b c d e) with cmp₃ k b d
--     ... | c<  = go a
--     ... | c≈₁ p rewrite p = just (proj₂ b)
--     ... | c>< = go c
--     ... | c≈₂ p rewrite p = just (proj₂ d)
--     ... | c>  = go e

--   fold : ∀ {n r} {R : Set r}
--          (f₃ : R → KV → R → KV → R → R)
--          (f₂ : R → KV → R → R) (l : R) →
--          BTree n → R
--   fold f₃ f₂ l = go
--     where
--     go : ∀ {n} → BTree n → _
--     go nil             = l
--     go (bt₁ a b c)     = f₂ (go a) b (go c)
--     go (bt₂ a b c d e) = f₃ (go a) b (go c) d (go e)

-- data Tree : Set (k ⊔ v) where
--   some : ∀ {n} → Sized.BTree n → Tree

-- private
--   repack-i : ∀ {n} → Sized.Inserted n → Tree
--   repack-i (Sized.keep t)     = some t
--   repack-i (Sized.push l x r) = some (Sized.bt₁ l x r)

--   repack-d : ∀ {n} → Sized.Deleted n → Tree
--   repack-d (Sized.keep t) = some t
--   repack-d (Sized.pull t) = some t

-- insertWith : (k : K) → V k → (V k → V k → V k) → Tree → Tree
-- insertWith k v f (some t) = repack-i (Sized.insertWith k v f t)

-- insert : (k : K) → V k → Tree → Tree
-- insert k v = insertWith k v const

-- delete : K → Tree → Tree
-- delete k (some t) = repack-d (Sized.delete k t)

-- fold : ∀ {r} {R : Set r}
--        (f₃ : R → KV → R → KV → R → R)
--        (f₂ : R → KV → R → R) (l : R) →
--        Tree → R
-- fold f₃ f₂ l (some t) = Sized.fold f₃ f₂ l t

-- empty : Tree
-- empty = some Sized.empty

-- singleton : (k : K) → V k → Tree
-- singleton k v = some (Sized.singleton k v)

-- lookup : (k : K) → Tree → Maybe (V k)
-- lookup k (some t) = Sized.lookup k t

-- _∈?_ : K → Tree → Bool
-- k ∈? t = maybeToBool (lookup k t)

-- fromList : List KV → Tree
-- fromList = foldr (uncurry insert) empty

-- toList : Tree → List KV
-- toList = DL.toList ∘ fold (λ a b c d e → a ++ b ∷ c ++ d ∷ e) (λ a b c → a ++ b ∷ c) []

-- unionWith : (∀ {k} → V k → V k → V k) → Tree → Tree → Tree
-- unionWith f t₁ t₂ = foldr (λ {(k , v) → insertWith k v f}) t₂ (toList t₁)

-- union : Tree → Tree → Tree
-- union = unionWith const
