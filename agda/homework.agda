{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import HoTT-UF-Agda public

open ℕ-order
open Arithmetic renaming (_+_ to _∔_ ; _×_ to _*_)


-- rewrite ≤ using ℕ-induction and prove it is equivalent
--

_≤'_ : ℕ → ℕ → 𝓤₀ ̇
_≤'_ = ℕ-recursion (ℕ → 𝓤₀ ̇ ) (λ _ → 𝟙) (λ _ h → ℕ-recursion (𝓤₀ ̇ ) 𝟘 (λ n _ → h n))

≤_eq_≤' : (x y : ℕ) → (x ≤ y) ＝ (x ≤' y)
≤_eq_≤' 0 n = refl 𝟙
≤_eq_≤' (succ n) 0 = refl 𝟘
≤_eq_≤' (succ n) (succ m) = ≤_eq_≤' n m


-- prove x ≤ y ⇔ Σ d : ℕ , x + d = y
--

le_imp_ex : (x y : ℕ) → x ≤ y → Σ (λ d → d ∔ x ＝ y)
le_imp_ex 0 0 h = (0 , refl 0)
le_imp_ex (succ n) 0 h = (0 , !𝟘 (0 ∔ (succ n) ＝ 0) h)
le_imp_ex (succ n) (succ m) h = (pr₁ s , ap succ (pr₂ s)) where
  s :  Σ (λ d → (d ∔ n) ＝ m)
  s = le_imp_ex n m h
le_imp_ex 0 (succ n) h = (succ n , p (succ n)) where
  p : (n : ℕ) -> (n ∔ 0) ＝ n
  p 0 = refl 0
  p (succ n) = ap succ (p n)

ex_imp_le : (x y : ℕ) → Σ (λ d → d ∔ x ＝ y) → x ≤ y
ex_imp_le 0 _ _ = ⋆
ex_imp_le (succ n) 0 (d , h) = !𝟘 ((succ n) ≤ 0) (a h) where
  a : (succ(d ∔ n) ＝ 0) → 𝟘
  a p = 𝟙-is-not-𝟘 (ap f p) where
    f : ℕ →  𝓤₀ ̇
    f 0 = 𝟘
    f (succ _) = 𝟙
ex_imp_le (succ m) (succ n) (d , p) = ex_imp_le m n (d , succ-lc p)


-- rewrite ℍ using 𝕁 without pattern matching
--

ℍ' : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ＝ y → 𝓥 ̇ )
   → B x (refl x)
   → (y : X) (p : x ＝ y) → B y p

ℍ' x B b y p = transport (B' x B) (𝕁 (type-of x) (λ x y p → (x , refl x) ＝ (y , p)) (λ u → refl ((u , refl u))) x y p) b where
  B' : {X : 𝓤 ̇ } → (x : X) → (B : (y : X) → x ＝ y → 𝓥 ̇ ) → ((Σ (λ y → x ＝ y)) → 𝓥 ̇ )
  B' _ B (y , q) = B y q

ℍs-agreement : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ＝ y → 𝓥 ̇ ) (b : B x (refl x)) (y : X) (p : x ＝ y)
   → ℍ x B b y p ＝ ℍ' x B b y p

ℍs-agreement x B b x (refl x) = refl b

-- write 𝕁 in terms of transport
--


-- define a version of identity composition that transports using the first argument
-- ???
_comp_ : {X : 𝓤 ̇ } → {x y z : X} → x ＝ y → y ＝ z → x ＝ z
p comp q = transport (_＝ rhs q) (inv (type-of (lhs p)) (lhs p) (rhs p) p) q where
  inv : (X : 𝓤 ̇ ) → (x y : X) → x ＝ y → y ＝ x
  inv X x x (refl x) = refl x


-- prove that ℕ has decidable equality using ℕ-induction
--

succ-not-fixed : (n : ℕ) → succ n ≠ n
succ-not-fixed 0 = positive-not-zero 0
succ-not-fixed (succ n) p = succ-not-fixed n (succ-lc p)

ℕ-has-decidable-equality' : has-decidable-equality ℕ
ℕ-has-decidable-equality' =
  ℕ-induction _
    (ℕ-induction _ (inl (refl 0)) (λ m _ → inr (≠-sym (positive-not-zero m))))
    (ℕ-induction _
      (λ d →
        ℕ-induction _
          (inr (positive-not-zero 0))
          (λ n →
              +-recursion
                (λ h → inr (λ q → succ-not-fixed n ((q ⁻¹) ∙ h)))
                (λ _ → +-recursion (inl ∘ (ap succ)) (λ z → inr (z ∘ succ-lc)) (d n))
          )
      )
      (λ m _ d →
        ℕ-induction _
          (inr (positive-not-zero (succ m)))
          (λ n _ → +-recursion (inl ∘ (ap succ)) (λ z → inr (z ∘ succ-lc)) (d n))
      )
    )


-- prove (X : 𝓤 ̇ ) → is-subsingleton X → ¬¬(is-singleton X + is-empty X)
--

dM : (X : 𝓤 ̇ ) → (Y : 𝓥 ̇ ) → ¬(X + Y) → (¬ X × ¬ Y)
dM X Y z = (z ∘ inl , z ∘ inr)

dn-EM : (X : 𝓤 ̇ ) → is-subsingleton X → ¬¬(is-singleton X + is-empty X)
dn-EM X f z = no-unicorns (X , (f , dM (is-singleton X) (is-empty X) z))


-- prove (X : 𝓤 ̇ ) → (R : 𝓥 ̇ )  → ((X + (X → R)) → R) → R
--

dnR-EM : (X : 𝓤 ̇ ) → (R : 𝓥 ̇ ) → ((X + (X → R)) → R) → R
dnR-EM _ _ f = (f ∘ inr) (f ∘ inl)


-- define the type of groups
--

left-inverse : {X : 𝓤 ̇ } → X → (X → X) → (X → X → X) → 𝓤 ̇ 
left-inverse e i _·_ = ∀ x → (i x) · x ＝ e 

right-inverse : {X : 𝓤 ̇ } → X → (X → X) → (X → X → X) → 𝓤 ̇
right-inverse e i _·_ = ∀ x → x · (i x) ＝ e

Group : (𝓤 : Universe) → 𝓤 ⁺ ̇
Group 𝓤 = Σ (X , f , op , e , l , r , a) ꞉ (monoids.Monoid 𝓤) , (Σ i ꞉ (X → X) , left-inverse e i op)

left-inverse-gives-right : {𝓤 : Universe} → (((X , f , · , e , ln , rn , a) , i , h) : Group 𝓤) → right-inverse e i ·
left-inverse-gives-right ((X , f , _·_ , e , ln , rn , a) , i , h) x =
  x · ix                ＝⟨ (ln (x · ix)) ⁻¹ ⟩
  e · (x · ix)          ＝⟨ ap (_· (x · ix)) ((h ix) ⁻¹) ⟩
  (iix · ix) · (x · ix) ＝⟨ (a (iix · ix) x ix) ⁻¹ ⟩
  ((iix · ix) · x) · ix ＝⟨ ap (_· ix) (a iix ix x) ⟩
  (iix · (ix · x)) · ix ＝⟨ ap ((_· ix) ∘ (iix ·_)) (h x) ⟩
  (iix · e) · ix        ＝⟨ ap (_· ix) (rn iix) ⟩
  iix · ix              ＝⟨ h ix ⟩
  e ∎ where
    ix = i x
    iix = i (i x)


-- define the types of precategory, strict category, and category as given in the hott book
--

Precategory : (𝓤 𝓥 : Universe) → (𝓤 ⁺ ⊔ 𝓥 ⁺) ̇ 
Precategory 𝓤 𝓥 =
  Σ Ob ꞉ 𝓤 ̇  , (
    Σ Hom ꞉ (Ob → Ob → 𝓥 ̇ ) , (
      Σ comp ꞉ ({A B C : Ob} → Hom A B → Hom B C → Hom A C) , (
        (X Y : Ob) →
          is-set (Hom X Y) × (
            Σ ident ꞉ (Hom X X) , (
              (f : Hom X Y) → (g : Hom Y X) → (comp ident f ＝ f) × (comp g ident ＝ g)
            )
          )
      )
    )
  )

Ob : {𝓤 𝓥 : Universe} → (C : Precategory 𝓤 𝓥) → 𝓤 ̇
Ob = pr₁

hom : {𝓤 𝓥 : Universe} → (C : Precategory 𝓤 𝓥) → (X Y : Ob C) → 𝓥 ̇
hom C = pr₁ (pr₂ C)

comp : {𝓤 𝓥 : Universe} → (C : Precategory 𝓤 𝓥) → {X Y Z : Ob C} → hom C X Y → hom C Y Z → hom C X Z
comp C = pr₁ (pr₂ (pr₂ C))

ident : {𝓤 𝓥 : Universe} → (C : Precategory 𝓤 𝓥) → (X : Ob C) → hom C X X
ident C X = pr₁ (pr₂ ((pr₂ (pr₂ (pr₂ C))) X X))

StrictCategory : (𝓤 𝓥 : Universe) → (𝓤 ⁺ ⊔ 𝓥 ⁺) ̇
StrictCategory 𝓤 𝓥 = Σ (Ob , _) ꞉ Precategory 𝓤 𝓥 , is-set Ob

Iso : {𝓤 𝓥 : Universe} → ((Ob , _) : Precategory 𝓤 𝓥) → (X Y : Ob) → 𝓥 ̇
Iso C X Y =
  Σ f ꞉ (hom C X Y) , (
    Σ g ꞉ (hom C Y X) , (
      ((comp C) f g ＝ ident C X) ×
      ((comp C) g f ＝ ident C Y)
    )
  )

Id→iso : {𝓤 𝓥 : Universe} → (C : Precategory 𝓤 𝓥) → (X Y : Ob C) → X ＝ Y → (Iso C X Y)
Id→iso C X X (refl X) = (ident C X , ident C X , p , p) where
  p : (comp C) (ident C X) (ident C X) ＝ ident C X
  p = pr₁ ((pr₂ (pr₂ ((pr₂ (pr₂ (pr₂ C))) X X))) (ident C X) (ident C X))


{-
Category : (𝓤 𝓥 : Universe) → (𝓤 ⁺ ⊔ 𝓥 ⁺) ̇
Category 𝓤 𝓥 = Σ C ꞉ Precategory , (
  Σ Iso→id ꞉ ({X Y : Ob C} → (Iso C X Y) → (X ＝ Y)) , (
    ((Iso→id ∘ Id→iso) ∼ id) ×
    ((Id→iso ∘ Iso→id) ~ id)
  )
)
-}



