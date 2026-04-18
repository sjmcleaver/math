{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import HoTT-UF-Agda public

open ℕ-order
open Arithmetic renaming (_+_ to _∔_ ; _×_ to _*_)



-- rewrite ≤ using ℕ-induction and prove it is equivalent
--

_≤'_ : ℕ → ℕ → 𝓤₀ ̇
_≤'_ = ℕ-iteration (ℕ → 𝓤₀ ̇ ) (λ _ → 𝟙) (λ h → ℕ-recursion (𝓤₀ ̇ ) 𝟘 (λ n _ → h n))

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

ℍ' x B b y p =
  (𝕁 (Σ z ꞉ _ , x ＝ z) (λ (z , q) (w , r) _ → B z q → B w r) (λ (z , q) → 𝑖𝑑 (B z q)) (x , refl x) (y , p))
  (𝕁 _ (λ x y p → (x , refl x) ＝ (y , p)) (λ u → refl ((u , refl u))) x y p) b

ℍs-agreement : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ＝ y → 𝓥 ̇ ) (b : B x (refl x)) (y : X) (p : x ＝ y)
   → ℍ x B b y p ＝ ℍ' x B b y p

ℍs-agreement x B b x (refl x) = refl b



-- write 𝕁 in terms of transport
--

𝕁'' : {X : 𝓤 ̇ } → (A : (x y : X) → x ＝ y → 𝓥 ̇ ) → ((x : X) → A x x (refl x)) → (x y : X) → (p : x ＝ y) → A x y p
𝕁'' A f x x (refl x) = transport (Σ-induction (A x)) (to-Σ-＝ (refl x , refl (refl x))) (f x)



-- define a version of identity composition that transports using the first argument
-- ???

_comp_ : {X : 𝓤 ̇ } → {x y z : X} → x ＝ y → y ＝ z → x ＝ z
p comp q = transport (_＝ rhs q) (inv (type-of (lhs p)) (lhs p) (rhs p) p) q where
  inv : (X : 𝓤 ̇ ) → (x y : X) → x ＝ y → y ＝ x
  inv X x x (refl x) = refl x



-- prove that refl gives a left and right neutral element of identity composition
--

refl-left-neutral : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → (refl x) ∙ p ＝ p
refl-left-neutral (refl x) = refl (refl x)

refl-right-neutral : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → p ∙ (refl y)＝ p
refl-right-neutral (refl y) = refl (refl y)



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
dM _ _ f = (f ∘ inl , f ∘ inr)

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
Group 𝓤 = Σ (X , _ , op , e , _) ꞉ (monoids.Monoid 𝓤) , (Σ i ꞉ (X → X) , left-inverse e i op)

left-inverse-gives-right : {𝓤 : Universe} → (((_ , _ , · , e , _ , _ , _) , i , h) : Group 𝓤) → right-inverse e i ·
left-inverse-gives-right ((_ , _ , _·_ , e , ln , rn , a) , i , h) x =
  x · ix                ＝⟨ (ln (x · ix)) ⁻¹ ⟩
  e · (x · ix)          ＝⟨ ap (_· (x · ix)) ((h ix) ⁻¹) ⟩
  (iix · ix) · (x · ix) ＝⟨ (a (iix · ix) x ix) ⁻¹ ⟩
  ((iix · ix) · x) · ix ＝⟨ ap (_· ix) (a iix ix x) ⟩
  (iix · (ix · x)) · ix ＝⟨ ap ((_· ix) ∘ (iix ·_)) (h x) ⟩
  (iix · e) · ix        ＝⟨ ap (_· ix) (rn iix) ⟩
  iix · ix              ＝⟨ h ix ⟩
  e                     ∎ where
    ix = i x
    iix = i (i x)

inverse-is-unique : {𝓤 : Universe} → (((X , _ , op , e , _) , i , h) : Group 𝓤) → (j : X → X)
                    → (left-inverse e j op) → i ∼ j
inverse-is-unique ((X , s , _·_ , e , ln , rn , a) , i , h) j k x =
  i x                 ＝⟨ (rn (i x)) ⁻¹ ⟩
  (i x) · e           ＝⟨ ap ((i x) ·_) p ⟩
  (i x) · (x · (j x)) ＝⟨ (a (i x) x (j x)) ⁻¹ ⟩
  ((i x) · x) · (j x) ＝⟨ ap (_· (j x)) (h x) ⟩
  e · (j x)           ＝⟨ ln (j x) ⟩
  j x                 ∎ where
    p : e ＝ (x · (j x))
    p = ((left-inverse-gives-right ((X , s , _·_ , e , ln , rn , a) , j , k)) x) ⁻¹



-- define the types of precategory, strict category, and category as given in the hott book
--

Precategory : (𝓤 𝓥 : Universe) → (𝓤 ⁺ ⊔ 𝓥 ⁺) ̇ 
Precategory 𝓤 𝓥 =
  Σ Ob ꞉ 𝓤 ̇  , (
    Σ Hom ꞉ (Ob → Ob → 𝓥 ̇ ) , (
      Σ ident ꞉ ((X : Ob) → Hom X X) , ( 
        Σ cmp ꞉ ((X Y Z : Ob) → Hom X Y → Hom Y Z → Hom X Z) , (
          (A B : Ob) → (f : Hom A B) →
            (is-set (Hom A B)) × (cmp A A B (ident A) f ＝ f) × (cmp A B B f (ident B) ＝ f)
        )
      )
    )
  )

Ob : {𝓤 𝓥 : Universe} → (C : Precategory 𝓤 𝓥) → 𝓤 ̇
Ob = pr₁

hom : {𝓤 𝓥 : Universe} → (C : Precategory 𝓤 𝓥) → (X Y : Ob C) → 𝓥 ̇
hom C = pr₁ (pr₂ C)

cmp : {𝓤 𝓥 : Universe} → (C : Precategory 𝓤 𝓥) → (X Y Z : Ob C) → hom C X Y → hom C Y Z → hom C X Z
cmp C  = pr₁ (pr₂ (pr₂ (pr₂ C)))

ident : {𝓤 𝓥 : Universe} → (C : Precategory 𝓤 𝓥) → (X : Ob C) → hom C X X
ident C = pr₁ (pr₂ (pr₂ C))

StrictCategory : (𝓤 𝓥 : Universe) → (𝓤 ⁺ ⊔ 𝓥 ⁺) ̇
StrictCategory 𝓤 𝓥 = Σ (Ob , _) ꞉ Precategory 𝓤 𝓥 , is-set Ob

Iso : {𝓤 𝓥 : Universe} → ((Ob , _) : Precategory 𝓤 𝓥) → (X Y : Ob) → 𝓥 ̇
Iso C X Y =
  Σ f ꞉ (hom C X Y) , (
    Σ g ꞉ (hom C Y X) , (
      ((cmp C X Y X) f g ＝ ident C X) ×
      ((cmp C Y X Y) g f ＝ ident C Y)
    )
  )

Id→iso : {𝓤 𝓥 : Universe} → (C : Precategory 𝓤 𝓥) → (X Y : Ob C) → X ＝ Y → (Iso C X Y)
Id→iso C X X (refl X) = (ident C X , ident C X , p , p) where
  p : (cmp C X X X) (ident C X) (ident C X) ＝ ident C X
  p = pr₁ (pr₂ ((pr₂ (pr₂ (pr₂ (pr₂ C)))) X X (ident C X)))


Category : (𝓤 𝓥 : Universe) → (𝓤 ⁺ ⊔ 𝓥 ⁺) ̇
Category 𝓤 𝓥 =
  Σ C ꞉ Precategory 𝓤 𝓥 , (
    Σ Iso→id ꞉ ((X Y : Ob C) → (Iso C X Y) → (X ＝ Y)) , (
      (X Y : Ob C) → (
        (((Iso→id X Y) ∘ (Id→iso C X Y)) ∼ id) ×
        (((Id→iso C X Y) ∘ (Iso→id X Y)) ∼ id)
      )
    )
  )

open basic-arithmetic-and-order

𝟙-is-set' : is-set 𝟙
𝟙-is-set' ⋆ ⋆ (refl ⋆) (refl ⋆) = refl (refl ⋆)

≤-is-set : (a b : ℕ) → (is-set (a ≤ b))
≤-is-set 0 0 = 𝟙-is-set'
≤-is-set 0 (succ n) = 𝟙-is-set'
≤-is-set (succ n) 0 = λ z _ → !𝟘 _ z
≤-is-set (succ m) (succ n) = ≤-is-set m n

≤-is-subsingleton : (a b : ℕ) → is-subsingleton (a ≤ b)
≤-is-subsingleton 0 0 = 𝟙-is-subsingleton
≤-is-subsingleton 0 (succ n) = 𝟙-is-subsingleton
≤-is-subsingleton (succ n) 0 = λ z _ → !𝟘 _ z
≤-is-subsingleton (succ m) (succ n) = ≤-is-subsingleton m n

PC-ℕ : Precategory 𝓤₀ 𝓤₀
PC-ℕ = (ℕ , _≤_ , ≤-refl , ≤-trans ,
  (λ a b f → (
    (≤-is-set a b) , 
    ≤-is-subsingleton a b (≤-trans a a b (≤-refl a) f) f ,
    ≤-is-subsingleton a b (≤-trans a b b f (≤-refl b)) f
  )))

SC-ℕ : StrictCategory 𝓤₀ 𝓤₀
SC-ℕ = (PC-ℕ , ℕ-is-set)

C-ℕ : Category 𝓤₀ 𝓤₀
C-ℕ = (PC-ℕ , Iso→id , (λ a b → (F a b , G a b))) where
  Iso→id : (a b : ℕ) → (Iso PC-ℕ a b) → (a ＝ b)
  Iso→id a b f = ≤-anti a b (pr₁ f) (pr₁ (pr₂ f))

  F : (a b : ℕ) → (p : a ＝ b) → (Iso→id a b (Id→iso PC-ℕ a b p)) ＝ p
  F a b p = ℕ-is-set a b (Iso→id a b (Id→iso PC-ℕ a b p)) p

  G : (a b : ℕ) → (f : Iso PC-ℕ a b) → (Id→iso PC-ℕ a b (Iso→id a b f)) ＝ f
  G a b _ = to-Σ-＝ (
    ≤-is-subsingleton a b _ _ , to-Σ-＝ (
    ≤-is-subsingleton b a _ _ , to-Σ-＝ (
    ≤-is-set a a _ _ _ _ ,
    ≤-is-set b b _ _ _ _)))

{-
PC-Set : (𝓤 : Universe) → Precategory 𝓤 𝓤
PC-Set = ?

C-Set : (𝓤 : Universe) → Category 𝓤 𝓤
C-Set = ?
-}

-- define the type of topological spaces
--
{-
P : (X : 𝓤 ̇ ) → 𝓤 ̇
P X = X → 𝟚

_and_ : 𝟚 → 𝟚 → 𝟚
₁ and ₁ = ₁
₁ and ₀ = ₀
₀ and _ = ₀

_or_ : 𝟚 → 𝟚 → 𝟚
₀ or ₀ = ₀
₀ or ₁ = ₁
₁ or _ = ₁

union : {X : 𝓤 ̇ } → P X → P X → P X
union u v x = (u x) and (v x)

intersection : {X : 𝓤 ̇ } → P X → P X → P X
intersection u v x = (u x) or (v x)

Union : {X : 𝓤 ̇ } → (C : P (P X)) → P X
Union C x = ?

-- need
-- (x : X) → (C : P (P X)) → decidable (Σ u ꞉ P X , (C u) and (u x))

Union-closed : {X : 𝓤 ̇ } → P (P X) → 𝓤 ̇
Union-closed {X} C = (S : P (P X)) → ((u : P X) → S u ＝ ₁ → C u ＝ ₁) → C (Union S) ＝ ₁

intersection-closed : {X : 𝓤 ̇ } → P (P X) → 𝓤 ̇ 
intersection-closed {X} C = (u v : P X) → C (intersection u v)

is-topology : {X : 𝓤 ̇ } → (T : P (P X)) → 𝓤 ̇ 
is-topology T =
  (T (λ _ → ₀) ＝ ₁) × (T (λ _ → ₁) ＝ ₁) × (Union-closed T) × (intersection-closed T)

TopologicalSpace : (𝓤 : Universe) → 𝓤 ⁺ ̇
TopologicalSpace 𝓤 = Σ X ꞉ 𝓤 ̇ , (Σ T ꞉ ((X → 𝟚) → 𝟚) , (is-topology T) × (is-set X))

-}



-- prove the associativity of identity compositions using 𝕁 and ℍ
--

∙assoc-𝕁 : (X : 𝓤 ̇ ) {x y z t : X} (p : x ＝ y) (q : y ＝ z) (r : z ＝ t) → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
∙assoc-𝕁 X {x} {y} {z} {t} p q r =
  (𝕁 X (λ a b s → (w w' : X) → (u : w ＝ a) → (v : b ＝ w') → ((u ∙ s) ∙ v ＝ u ∙ (s ∙ v)))
    (λ a w w' u v → (ap (_∙ v) (refl-right-neutral u)) ∙ (ap (u ∙_) ((refl-left-neutral v) ⁻¹))) y z q)
    x t p r


∙assoc-ℍ : (X : 𝓤 ̇ ) {x y z t : X} (p : x ＝ y) (q : y ＝ z) (r : z ＝ t) → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
∙assoc-ℍ X {x} {y} {z} {t} p q r =
  (ℍ y (λ a s → (w w' : X) → (u : w ＝ y) → (v : a ＝ w') → ((u ∙ s) ∙ v ＝ u ∙ (s ∙ v)))
    (λ w w' u v → (ap (_∙ v) (refl-right-neutral u)) ∙ (ap (u ∙_) ((refl-left-neutral v) ⁻¹))) z q)
    x t p r



-- prove that 𝟙 has minimal hlevel 0, 𝟘 has minimal hlevel 1, and ℕ has minimal hlevel 0
--

𝟙-has-minimal-hlevel-0 : 𝟙 has-minimal-hlevel 0
𝟙-has-minimal-hlevel-0 = 𝟙-is-singleton

𝟘-has-minimal-hlevel-1 : 𝟘 has-minimal-hlevel 1
𝟘-has-minimal-hlevel-1 = ((λ x → !𝟘 _ x) , (λ z → !𝟘 _ (pr₁ z)))

ℕ-is-set' : is-set ℕ
ℕ-is-set' 0 0 (refl 0) p = g p where
  g : (p : 0 ＝ 0) → refl 0 ＝ p
  g (refl 0) = refl (refl 0)
ℕ-is-set' 0 (succ n) p = !𝟘 _ (positive-not-zero n (p ⁻¹))
ℕ-is-set' (succ n) 0 p = !𝟘 _ (positive-not-zero n p)
ℕ-is-set' (succ m) (succ n) p q =
  (f m n p) ∙ (ap (ap succ) (ℕ-is-set' m n (ap pred p) (ap pred q))) ∙ ((f m n q) ⁻¹) where
    f : (a b : ℕ) (p : succ a ＝ succ b) → p ＝ ap succ (ap pred p)
    f a a (refl (succ a)) = refl (refl (succ a))

ℕ-is-not-hlevel-1 : ¬(ℕ is-of-hlevel 1)
ℕ-is-not-hlevel-1 z = positive-not-zero 0 (pr₁ (z 1 0))

ℕ-has-minimal-hlevel-2 : ℕ has-minimal-hlevel 2
ℕ-has-minimal-hlevel-2 = (sets-are-of-hlevel-2 ℕ ℕ-is-set' , ℕ-is-not-hlevel-1)



-- construct a term of ℕ ◁ ℕ using pred as the retraction. construct other terms of ℕ ◁ ℕ.
--

pred-retraction : ℕ ◁ ℕ
pred-retraction = (pred , succ , refl)

pred²-retraction : ℕ ◁ ℕ
pred²-retraction = (pred ∘ pred , succ ∘ succ , refl)

halve : ℕ → ℕ
halve 0 = 0
halve 1 = 0
halve (succ (succ n)) = (halve n) ∔ 1

double : ℕ → ℕ
double n = 2 * n

double-is-section : (n : ℕ) →  halve (double n) ＝ n
double-is-section 0 = refl 0
double-is-section (succ n) = (ap halve (+-comm 2 (2 * n))) ∙ (ap succ (double-is-section n))

halve-retraction : ℕ ◁ ℕ
halve-retraction = (halve , double , double-is-section)



-- various exercises
--

EX-subsingleton-criterion : {X : 𝓤 ̇ } → (X → is-singleton X) → is-subsingleton X
EX-subsingleton-criterion f x y = ((pr₂ (f x)) x) ⁻¹ ∙ (pr₂ (f x)) y

EX-subsingleton-criterion' : {X : 𝓤 ̇ } → (X → is-subsingleton X) → is-subsingleton X
EX-subsingleton-criterion' f x = f x x

EX-retract-of-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → Y ◁ X → is-subsingleton X → is-subsingleton Y
EX-retract-of-subsingleton (r , s , i) f y z = i y ⁻¹ ∙ ap r (f (s y) (s z)) ∙ i z

EX-lc-maps-reflect-subsingletons : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → left-cancellable f → is-subsingleton Y
                                   → is-subsingleton X
EX-lc-maps-reflect-subsingletons f l s x x' = l (s (f x) (f x'))

EX-sections-are-lc : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (s : X → A) → has-retraction s → left-cancellable s
EX-sections-are-lc s (r , i) {x} {x'} p = i x ⁻¹ ∙ ap r p ∙ i x'

EX-equivs-have-retractions : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-retraction f
EX-equivs-have-retractions f e =
  (λ y → pr₁ (pr₁ (e y))) ,
  (λ x → pr₁ (from-Σ-＝ ((pr₂ (e (f x))) (x , refl (f x)))))

EX-equivs-have-sections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-section f
EX-equivs-have-sections f e = (λ y → pr₁ (pr₁ (e y))) , (λ y → pr₂ (pr₁ (e y)))

EX-equivs-are-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → left-cancellable f
EX-equivs-are-lc f e = EX-sections-are-lc f (EX-equivs-have-retractions f e)

EX-equiv-to-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → is-subsingleton Y → is-subsingleton X
EX-equiv-to-subsingleton (f , e) s = EX-retract-of-subsingleton (inverse f e , f , inverses-are-retractions f e) s

EX-comp-inverses : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y) (g : Y → Z) (i : is-equiv f) (j : is-equiv g) (f' : Y → X)
                   (g' : Z → Y) → f' ∼ inverse f i → g' ∼ inverse g j → f' ∘ g' ∼ inverse (g ∘ f) (∘-is-equiv j i)
EX-comp-inverses f g i j f' g' u v z = u (g' z) ∙ ap (inverse f i) (v z) ∙ inverse-of-∘ f g i j z

EX-equiv-to-set : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → is-set Y → is-set X
EX-equiv-to-set X Y (f , e) s x x' p p' =
  p                       ＝⟨ (G x x' p) ⁻¹ ⟩
  F x x' (ap (g ∘ f) p)   ＝⟨ ap (F x x') (ap-∘ f g p) ⟩
  F x x' (ap g (ap f p))  ＝⟨ ap ((F x x') ∘ (ap g)) (s (f x) (f x') (ap f p) (ap f p')) ⟩
  F x x' (ap g (ap f p')) ＝⟨ ap (F x x') ((ap-∘ f g p') ⁻¹) ⟩
  F x x' (ap (g ∘ f) p')  ＝⟨ G x x' p' ⟩
  p'                      ∎ where
    g = inverse f e

    i : (t : X) → g (f t) ＝ t
    i = inverses-are-retractions f e

    F : (t t' : X) → g (f t) ＝ g (f t') → t ＝ t'
    F t t' q = (i t) ⁻¹ ∙ q ∙ i t'

    G : (t t' : X) → (q : t ＝ t') → F t t' (ap (g ∘ f) q) ＝ q
    G t t (refl t) =
      i t ⁻¹ ∙ refl ((g ∘ f) t) ∙ i t ＝⟨ refl-right ⟩
      i t ⁻¹ ∙ i t                    ＝⟨ ⁻¹-left∙ (i t) ⟩
      refl t                          ∎

EX-sections-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y) → has-retraction f → g ∼ f → has-retraction g
EX-sections-closed-under-∼ f g (r , i) e = (r , (λ x → ap r (e x) ∙ i x))

EX-retractions-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y) → has-section f → g ∼ f → has-section g
EX-retractions-closed-under-∼ f g (s , i) e = (s , (λ x → e (s x) ∙ i x))

EX-one-inverse : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X → Y) (r s : Y → X) → (r ∘ f ∼ id) → (f ∘ s ∼ id) → r ∼ s
EX-one-inverse X Y f r s i j y = ap r ((j y) ⁻¹) ∙ i (s y)

EX-joyal-equivs-are-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-joyal-equiv f → invertible f
EX-joyal-equivs-are-invertible f ((s , i) , (r , j)) = (r , (j , (λ x → ap f (p x) ∙ (i x)))) where
  p = EX-one-inverse (domain f) (codomain f) f r s j i

EX-joyal-equivs-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-joyal-equiv f → is-equiv f
EX-joyal-equivs-are-equivs {X} {Y} f ((s , i) , (r , j)) = invertibles-are-equivs f (s , h , i) where
  h : (x : domain f) → s (f x) ＝ x
  h x = EX-one-inverse (domain f) (codomain f) f r s j i (f x) ⁻¹ ∙ j x


{-


invertibles-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → invertible f → is-joyal-equiv f

equivs-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                        → is-equiv f → is-joyal-equiv f


equivs-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y}
                      → is-equiv f
                      → g ∼ f
                      → is-equiv g


equiv-to-singleton' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    → X ≃ Y → is-singleton X → is-singleton Y


subtypes-of-sets-are-sets : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
                          → left-cancellable m → is-set Y → is-set X


pr₁-lc : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
       → ((x : X) → is-subsingleton (A x))
       → left-cancellable (λ (t : Σ A) → pr₁ t)


subsets-of-sets-are-sets : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                         → is-set X
                         → ((x : X) → is-subsingleton (A x))
                         → is-set (Σ x ꞉ X , A x)


to-subtype-＝ : {X : 𝓦 ̇ } {A : X → 𝓥 ̇ }
               {x y : X} {a : A x} {b : A y}
             → ((x : X) → is-subsingleton (A x))
             → x ＝ y
             → (x , a) ＝ (y , b)


pr₁-is-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
             → ((x : X) → is-singleton (A x))
             → is-equiv (λ (t : Σ A) → pr₁ t)


pr₁-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
      → ((x : X) → is-singleton (A x))
      → Σ A ≃ X

pr₁-≃ i = pr₁ , pr₁-is-equiv i


ΠΣ-distr-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
           → (Π x ꞉ X , Σ a ꞉ A x , P x a)
           ≃ (Σ f ꞉ Π A , Π x ꞉ X , P x (f x))


Σ-assoc : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : Σ Y → 𝓦 ̇ }
        → Σ Z ≃ (Σ x ꞉ X , Σ y ꞉ Y x , Z (x , y))


⁻¹-≃ : {X : 𝓤 ̇ } (x y : X) → (x ＝ y) ≃ (y ＝ x)


singleton-types-≃ : {X : 𝓤 ̇ } (x : X) → singleton-type' x ≃ singleton-type x


singletons-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → is-singleton X → is-singleton Y → X ≃ Y


maps-of-singletons-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                              → is-singleton X → is-singleton Y → is-equiv f


logically-equivalent-subsingletons-are-equivalent : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                                                  → is-subsingleton X
                                                  → is-subsingleton Y
                                                  → X ⇔ Y
                                                  → X ≃ Y

singletons-are-equivalent : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                          → is-singleton X
                          → is-singleton Y
                          → X ≃ Y


NatΣ-fiber-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (φ : Nat A B)
                   (x : X) (b : B x)
                 → fiber (φ x) b ≃ fiber (NatΣ φ) (x , b)


NatΣ-equiv-gives-fiberwise-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                                   (φ : Nat A B)
                                 → is-equiv (NatΣ φ)
                                 → ((x : X) → is-equiv (φ x))


Σ-is-subsingleton : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                  → is-subsingleton X
                  → ((x : X) → is-subsingleton (A x))
                  → is-subsingleton (Σ A)


×-is-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → is-singleton X
                  → is-singleton Y
                  → is-singleton (X × Y)


×-is-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → is-subsingleton X
                  → is-subsingleton Y
                  → is-subsingleton (X × Y)

×-is-subsingleton' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → ((Y → is-subsingleton X) × (X → is-subsingleton Y))
                   → is-subsingleton (X × Y)


×-is-subsingleton'-back : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                        → is-subsingleton (X × Y)
                        → (Y → is-subsingleton X) × (X → is-subsingleton Y)


ap₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x x' : X} {y y' : Y}
    → x ＝ x' → y ＝ y' → f x y ＝ f x' y'


-}
