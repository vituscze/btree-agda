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

  open Extended-key public
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


  data Deleted⁺ (lb ub : Key⁺) : ℕ → Set (k ⊔ v ⊔ ℓ) where
    keep : ∀ {n} (t : BTree⁺ lb ub n) → Deleted⁺ lb ub n
    pull : ∀ {n} (t : BTree⁺ lb ub n) → Deleted⁺ lb ub (suc n)

  data Replace⁺ (lb ub : Key⁺) : ℕ → Set (k ⊔ v ⊔ ℓ) where
    keep : ∀ {n} (x : KV) → [ proj₁ x ] <⁺ ub → BTree⁺ lb [ proj₁ x ] n → Replace⁺ lb ub n
    pull : ∀ {n} (x : KV) → [ proj₁ x ] <⁺ ub → BTree⁺ lb [ proj₁ x ] n → Replace⁺ lb ub (suc n)
    leaf :                                                                Replace⁺ lb ub 0

  extend : ∀ {n lb₁ lb₂ ub} → lb₁ <⁺ lb₂ → BTree⁺ lb₂ ub n → BTree⁺ lb₁ ub n
  extend {lb₁ = lb₁} p (nil {p = p₁}) = nil {p = trans⁺ lb₁ p p₁}
  extend p (bt₁ b a c)     = bt₁ b (extend p a) c
  extend p (bt₂ b d a c e) = bt₂ b d (extend p a) c e

  delete : ∀ {n} → K → BTree⁺ ⊥⁺ ⊤⁺ n → Deleted⁺ ⊥⁺ ⊤⁺ n
  delete k = search
    where
    replace : ∀ {n lb ub} → BTree⁺ lb ub n → Replace⁺ lb ub n
    replace nil = leaf

    replace (bt₁ b a c) with replace c
    replace (bt₁ b a c) | keep x q c′ = keep x q (bt₁ b a c′)
    replace (bt₁ b (bt₁ a₂ a₁ a₃) c)       | pull x q c′ = pull x q (bt₂ a₂ b a₁ a₃ c′)
    replace (bt₁ b (bt₂ a₂ a₄ a₁ a₃ a₅) c) | pull x q c′ = keep x q (bt₁ a₄ (bt₁ a₂ a₁ a₃) (bt₁ b a₅ c′))
    replace (bt₁ b a (nil {p = p})) | leaf = pull b p a

    replace (bt₂ b d a c e) with replace e
    replace (bt₂ b d a c e) | keep x q e′ = keep x q (bt₂ b d a c e′)
    replace (bt₂ b d a (bt₁ c₂ c₁ c₃) e)       | pull x q e′ = keep x q (bt₁ b a (bt₂ c₂ d c₁ c₃ e′))
    replace (bt₂ b d a (bt₂ c₂ c₄ c₁ c₃ c₅) e) | pull x q e′ = keep x q (bt₂ b c₄ a (bt₁ c₂ c₁ c₃) (bt₁ d c₅ e′))
    replace (bt₂ b d a c (nil {p = p})) | leaf = keep d p (bt₁ b a c)

    search : ∀ {n lb ub} → BTree⁺ lb ub n → Deleted⁺ lb ub n
    search (nil {p = p}) = keep (nil {p = p})

    search (bt₁ b a c) with cmp₂ k b
    search (bt₁ b a c) | c< p with search a
    search (bt₁ b a c) | c< p | keep a′ = keep (bt₁ b a′ c)
    search (bt₁ b a (bt₁ c₂ c₁ c₃))       | c< p | pull a′ = pull (bt₂ b c₂ a′ c₁ c₃)
    search (bt₁ b a (bt₂ c₂ c₄ c₁ c₃ c₅)) | c< p | pull a′ = keep (bt₁ c₂ (bt₁ b a′ c₁) (bt₁ c₄ c₃ c₅))
    search (bt₁ b a c) | c≈ p with replace a
    search (bt₁ b a c) | c≈ p | keep x q a′ = keep (bt₁ x a′ (extend q c))
    search (bt₁ b a (bt₁ c₂ c₁ c₃))       | c≈ p | pull x q a′ = pull (bt₂ x c₂ a′ (extend q c₁) c₃)
    search (bt₁ b a (bt₂ c₂ c₄ c₁ c₃ c₅)) | c≈ p | pull x q a′ = keep (bt₁ c₂ (bt₁ x a′ (extend q c₁)) (bt₁ c₄ c₃ c₅))
    search {lb = lb} (bt₁ b (nil {p = p₁}) (nil {p = p₂})) | c≈ p | leaf = pull (nil {p = trans⁺ lb p₁ p₂})
    search (bt₁ b a c) | c> p with search c
    search (bt₁ b a c) | c> p | keep c′ = keep (bt₁ b a c′)
    search (bt₁ b (bt₁ a₂ a₁ a₃) c)       | c> p | pull c′ = pull (bt₂ a₂ b a₁ a₃ c′)
    search (bt₁ b (bt₂ a₂ a₄ a₁ a₃ a₅) c) | c> p | pull c′ = keep (bt₁ a₄ (bt₁ a₂ a₁ a₃) (bt₁ b a₅ c′))

    search (bt₂ b d a c e) with cmp₃ k b d
    search (bt₂ b d a c e) | c<  p with search a
    search (bt₂ b d a c e) | c<  p | keep a′ = keep (bt₂ b d a′ c e)
    search (bt₂ b d a (bt₁ c₂ c₁ c₃) e)       | c<  p | pull a′ = keep (bt₁ d (bt₂ b c₂ a′ c₁ c₃) e)
    search (bt₂ b d a (bt₂ c₂ c₄ c₁ c₃ c₅) e) | c<  p | pull a′ = keep (bt₂ c₂ d (bt₁ b a′ c₁) (bt₁ c₄ c₃ c₅) e)
    search (bt₂ b d a c e) | c≈₁ p with replace a
    search (bt₂ b d a c e) | c≈₁ p | keep x q a′ = keep (bt₂ x d a′ (extend q c) e)
    search (bt₂ b d a (bt₁ c₂ c₁ c₃) e)       | c≈₁ p | pull x q a′ = keep (bt₁ d (bt₂ x c₂ a′ (extend q c₁) c₃) e)
    search (bt₂ b d a (bt₂ c₂ c₄ c₁ c₃ c₅) e) | c≈₁ p | pull x q a′ = keep (bt₂ c₂ d (bt₁ x a′ (extend q c₁)) (bt₁ c₄ c₃ c₅) e)
    search {lb = lb} (bt₂ b d (nil {p = p₁}) (nil {p = p₂}) e) | c≈₁ p | leaf = keep (bt₁ d (nil {p = trans⁺ lb p₁ p₂}) e)
    search (bt₂ b d a c e) | c>< p q with search c
    search (bt₂ b d a c e) | c>< p q | keep c′ = keep (bt₂ b d a c′ e)
    search (bt₂ b d a c (bt₁ e₂ e₁ e₃))       | c>< p q | pull c′ = keep (bt₁ b a (bt₂ d e₂ c′ e₁ e₃))
    search (bt₂ b d a c (bt₂ e₂ e₄ e₁ e₃ e₅)) | c>< p q | pull c′ = keep (bt₂ b e₂ a (bt₁ d c′ e₁) (bt₁ e₄ e₃ e₅))
    search (bt₂ b d a c e) | c≈₂ p with replace c
    search (bt₂ b d a c e) | c≈₂ p | keep x q c′ = keep (bt₂ b x a c′ (extend q e))
    search (bt₂ b d a c (bt₁ e₂ e₁ e₃))       | c≈₂ p | pull x q c′ = keep (bt₁ b a (bt₂ x e₂ c′ (extend q e₁) e₃))
    search (bt₂ b d a c (bt₂ e₂ e₄ e₁ e₃ e₅)) | c≈₂ p | pull x q c′ = keep (bt₂ b e₂ a (bt₁ x c′ (extend q e₁)) (bt₁ e₄ e₃ e₅))
    search {ub = ub} (bt₂ b d a (nil {p = p₁}) (nil {p = p₂})) | c≈₂ p | leaf = keep (bt₁ b a (nil {p = trans⁺ [ proj₁ b ] {[ proj₁ d ]} {ub} p₁ p₂}))
    search (bt₂ b d a c e) | c>  p with search e
    search (bt₂ b d a c e) | c> p | keep e′ = keep (bt₂ b d a c e′)
    search (bt₂ b d a (bt₁ c₂ c₁ c₃) e)       | c>  p | pull e′ = keep (bt₁ b a (bt₂ c₂ d c₁ c₃ e′))
    search (bt₂ b d a (bt₂ c₂ c₄ c₁ c₃ c₅) e) | c>  p | pull e′ = keep (bt₂ b c₄ a (bt₁ c₂ c₁ c₃) (bt₁ d c₅ e′))


  empty : BTree⁺ ⊥⁺ ⊤⁺ 0
  empty = nil

  singleton : (k : K) → V k → BTree⁺ ⊥⁺ ⊤⁺ 1
  singleton k v = bt₁ (k , v) nil nil

  lookup : ∀ {n} → (k : K) → BTree⁺ ⊥⁺ ⊤⁺ n → Maybe (V k)
  lookup k = go
    where
    go : ∀ {n lb ub} → BTree⁺ lb ub n → Maybe (V k)
    go nil = nothing

    go (bt₁ b a c) with cmp₂ k b
    ... | c< _ = go a
    ... | c≈ p rewrite p = just (proj₂ b)
    ... | c> _ = go c

    go (bt₂ b d a c e) with cmp₃ k b d
    ... | c<  _  = go a
    ... | c≈₁ p rewrite p = just (proj₂ b)
    ... | c>< _ _ = go c
    ... | c≈₂ p rewrite p = just (proj₂ d)
    ... | c>  _ = go e

  fold : ∀ {n r} {R : Set r}
         (f₃ : KV → KV → R → R → R → R)
         (f₂ : KV → R → R → R) (l : R) →
         BTree⁺ ⊥⁺ ⊤⁺ n → R
  fold {R = R} f₃ f₂ l = go
    where
    go : ∀ {n lb ub} → BTree⁺ lb ub n → R
    go nil             = l
    go (bt₁ b a c)     = f₂ b (go a) (go c)
    go (bt₂ b d a c e) = f₃ b d (go a) (go c) (go e)

data Tree : Set (k ⊔ v ⊔ ℓ) where
  some : let open Sized
         in ∀ {n} → BTree⁺ ⊥⁺ ⊤⁺ n → Tree

private
  module _ where
    open Sized

    repack-i : ∀ {n} → Inserted⁺ ⊥⁺ ⊤⁺ n → Tree
    repack-i (Sized.keep t)     = some t
    repack-i (Sized.push l x r) = some (Sized.bt₁ l x r)

    repack-d : ∀ {n} → Deleted⁺ ⊥⁺ ⊤⁺ n → Tree
    repack-d (Sized.keep t) = some t
    repack-d (Sized.pull t) = some t

insertWith : (k : K) → V k → (V k → V k → V k) → Tree → Tree
insertWith k v f (some t) = repack-i (Sized.insertWith⁺ k v f t)

insert : (k : K) → V k → Tree → Tree
insert k v = insertWith k v const

delete : K → Tree → Tree
delete k (some t) = repack-d (Sized.delete k t)

fold : ∀ {r} {R : Set r}
       (f₃ : KV → KV → R → R → R → R)
       (f₂ : KV → R → R → R) (l : R) →
       Tree → R
fold f₃ f₂ l (some t) = Sized.fold f₃ f₂ l t

empty : Tree
empty = some Sized.empty

singleton : (k : K) → V k → Tree
singleton k v = some (Sized.singleton k v)

lookup : (k : K) → Tree → Maybe (V k)
lookup k (some t) = Sized.lookup k t

_∈?_ : K → Tree → Bool
k ∈? t = maybeToBool (lookup k t)

fromList : List KV → Tree
fromList = foldr (uncurry insert) empty

toList : Tree → List KV
toList = DL.toList ∘ fold (λ b d a c e → a ++ b ∷ c ++ d ∷ e) (λ b a c → a ++ b ∷ c) []

unionWith : (∀ {k} → V k → V k → V k) → Tree → Tree → Tree
unionWith f t₁ t₂ = foldr (λ {(k , v) → insertWith k v f}) t₂ (toList t₁)

union : Tree → Tree → Tree
union = unionWith const
