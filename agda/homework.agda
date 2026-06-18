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
le_imp_ex 0 0 h = 0 , refl 0
le_imp_ex (succ n) 0 h = 0 , !𝟘 (0 ∔ (succ n) ＝ 0) h
le_imp_ex 0 (succ n) h = succ n , refl _
le_imp_ex (succ n) (succ m) h = pr₁ s , ap succ (pr₂ s) where
  s :  Σ (λ d → (d ∔ n) ＝ m)
  s = le_imp_ex n m h

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

refl-left-neutral : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → refl x ∙ p ＝ p
refl-left-neutral (refl x) = refl (refl x)

refl-right-neutral : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → p ∙ refl y ＝ p
refl-right-neutral (refl x) = refl (refl x)



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
                (λ h → inr (λ q → succ-not-fixed n (q ⁻¹ ∙ h)))
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
dM _ _ f = f ∘ inl , f ∘ inr

dn-EM : (X : 𝓤 ̇ ) → is-subsingleton X → ¬¬(is-singleton X + is-empty X)
dn-EM X f z = no-unicorns (X , (f , dM (is-singleton X) (is-empty X) z))



-- prove (X : 𝓤 ̇ ) → (R : 𝓥 ̇ )  → ((X + (X → R)) → R) → R
--

dnR-EM : (X : 𝓤 ̇ ) → (R : 𝓥 ̇ ) → ((X + (X → R)) → R) → R
dnR-EM _ _ f = (f ∘ inr) (f ∘ inl)



-- define the type of groups
--

left-inverse : {X : 𝓤 ̇ } → X → (X → X) → (X → X → X) → 𝓤 ̇ 
left-inverse e i _·_ = ∀ x → i x · x ＝ e 

right-inverse : {X : 𝓤 ̇ } → X → (X → X) → (X → X → X) → 𝓤 ̇
right-inverse e i _·_ = ∀ x → x · i x ＝ e

Group : (𝓤 : Universe) → 𝓤 ⁺ ̇
Group 𝓤 = Σ (X , _ , op , e , _) ꞉ (monoids.Monoid 𝓤) , (Σ i ꞉ (X → X) , left-inverse e i op)

left-inverse-gives-right : {𝓤 : Universe} → (((_ , _ , · , e , _) , i , h) : Group 𝓤) → right-inverse e i ·
left-inverse-gives-right ((_ , _ , _·_ , e , ln , rn , a) , i , h) x =
  x · ix                ＝⟨ ln (x · ix) ⁻¹ ⟩
  e · (x · ix)          ＝⟨ ap (_· (x · ix)) (h ix ⁻¹) ⟩
  (iix · ix) · (x · ix) ＝⟨ a (iix · ix) x ix ⁻¹ ⟩
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
  i x                 ＝⟨ rn (i x) ⁻¹ ⟩
  (i x) · e           ＝⟨ ap ((i x) ·_) p ⟩
  (i x) · (x · (j x)) ＝⟨ a (i x) x (j x) ⁻¹ ⟩
  ((i x) · x) · (j x) ＝⟨ ap (_· (j x)) (h x) ⟩
  e · (j x)           ＝⟨ ln (j x) ⟩
  j x                 ∎ where
    p : e ＝ (x · (j x))
    p = (left-inverse-gives-right ((X , s , _·_ , e , ln , rn , a) , j , k)) x ⁻¹



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

≤-is-set : (a b : ℕ) → is-set (a ≤ b)
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
PC-ℕ = ℕ , _≤_ , ≤-refl , ≤-trans ,
  (λ a b f → (
    (≤-is-set a b) , 
    ≤-is-subsingleton a b (≤-trans a a b (≤-refl a) f) f ,
    ≤-is-subsingleton a b (≤-trans a b b f (≤-refl b)) f
  ))

SC-ℕ : StrictCategory 𝓤₀ 𝓤₀
SC-ℕ = PC-ℕ , ℕ-is-set

C-ℕ : Category 𝓤₀ 𝓤₀
C-ℕ = PC-ℕ , Iso→id , (λ a b → (F a b , G a b)) where
  Iso→id : (a b : ℕ) → Iso PC-ℕ a b → a ＝ b
  Iso→id a b f = ≤-anti a b (pr₁ f) (pr₁ (pr₂ f))

  F : (a b : ℕ) → (p : a ＝ b) → Iso→id a b (Id→iso PC-ℕ a b p) ＝ p
  F a b p = ℕ-is-set a b (Iso→id a b (Id→iso PC-ℕ a b p)) p

  G : (a b : ℕ) → (f : Iso PC-ℕ a b) → (Id→iso PC-ℕ a b (Iso→id a b f)) ＝ f
  G a b _ = to-Σ-＝ (
    ≤-is-subsingleton a b _ _ , to-Σ-＝ (
    ≤-is-subsingleton b a _ _ , to-Σ-＝ (
    ≤-is-set a a _ _ _ _ ,
    ≤-is-set b b _ _ _ _)))


{-

PC-Set : (𝓤 : Universe) → Precategory (𝓤 ⁺) 𝓤
PC-Set 𝓤 = ((Σ A ꞉ 𝓤 ̇  , is-set A) , (λ (X , _) (Y , _) → (X → Y)) , (λ _ → id) , ((λ _ _ _ → (λ f g → g ∘ f)) , (λ (A , a) (B , b) f → Π-is-set (univalence-gives-hfunext (ua _)) (λ _ → b) , (refl _ , refl _))))

C-Set : (𝓤 : Universe) → Category 𝓤 𝓤
C-Set = ?

-}

-- define the type of topological spaces
--

{-

intersection : {X : 𝓤 ̇ } → 𝓟 X → 𝓟 X → 𝓟 X
intersection u v x = ((u x holds) + (v x holds)) , ?

Union : {X : 𝓤 ̇ } → 𝓟 (𝓟 X) → 𝓟 X
Union {X = X} C x = lower (Σ u ꞉ (𝓟 X) , ((u x holds) × (C u holds))) , ?

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
  (𝕁 X (λ a b s → (w w' : X) → (u : w ＝ a) → (v : b ＝ w') → (u ∙ s) ∙ v ＝ u ∙ (s ∙ v))
    (λ a w w' u v → ap (_∙ v) (refl-right-neutral u) ∙ ap (u ∙_) (refl-left-neutral v ⁻¹)) y z q)
    x t p r


∙assoc-ℍ : (X : 𝓤 ̇ ) {x y z t : X} (p : x ＝ y) (q : y ＝ z) (r : z ＝ t) → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
∙assoc-ℍ X {x} {y} {z} {t} p q r =
  (ℍ y (λ a s → (w w' : X) → (u : w ＝ y) → (v : a ＝ w') → (u ∙ s) ∙ v ＝ u ∙ (s ∙ v))
    (λ w w' u v → ap (_∙ v) (refl-right-neutral u) ∙ ap (u ∙_) (refl-left-neutral v ⁻¹)) z q)
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
  f m n p ∙ ap (ap succ) (ℕ-is-set' m n (ap pred p) (ap pred q)) ∙ f m n q ⁻¹ where
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
EX-subsingleton-criterion f x y = (pr₂ (f x)) x ⁻¹ ∙ (pr₂ (f x)) y

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
    F t t' q = i t ⁻¹ ∙ q ∙ i t'

    G : (t t' : X) → (q : t ＝ t') → F t t' (ap (g ∘ f) q) ＝ q
    G t t (refl t) =
      i t ⁻¹ ∙ refl ((g ∘ f) t) ∙ i t ＝⟨ refl-right ⟩
      i t ⁻¹ ∙ i t                    ＝⟨ ⁻¹-left∙ (i t) ⟩
      refl t                          ∎

-- EX-equiv-to-set' : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → is-set Y → is-set X
-- EX-equiv-to-set' X Y E S x x (refl x) p = {!!}


EX-sections-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y) → has-retraction f → g ∼ f → has-retraction g
EX-sections-closed-under-∼ f g (r , i) e = (r , (λ x → ap r (e x) ∙ i x))

EX-retractions-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y) → has-section f → g ∼ f → has-section g
EX-retractions-closed-under-∼ f g (s , i) e = (s , (λ x → e (s x) ∙ i x))

EX-one-inverse : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X → Y) (r s : Y → X) → (r ∘ f ∼ id) → (f ∘ s ∼ id) → r ∼ s
EX-one-inverse X Y f r s i j y = ap r ((j y) ⁻¹) ∙ i (s y)

EX-joyal-equivs-are-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-joyal-equiv f → invertible f
EX-joyal-equivs-are-invertible f ((s , i) , (r , j)) =
  (r , (j , (λ x → ap f ((EX-one-inverse (domain f) (codomain f) f r s j i) x) ∙ (i x))))

EX-joyal-equivs-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-joyal-equiv f → is-equiv f
EX-joyal-equivs-are-equivs {X} {Y} f ((s , i) , (r , j)) =
  invertibles-are-equivs f (s , (λ x → EX-one-inverse (domain f) (codomain f) f r s j i (f x) ⁻¹ ∙ j x) , i)

EX-invertibles-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → invertible f → is-joyal-equiv f
EX-invertibles-are-joyal-equivs _ (g , i , j) = ((g , j) , (g , i))

EX-equivs-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → is-joyal-equiv f
EX-equivs-are-joyal-equivs f e = EX-invertibles-are-joyal-equivs f (equivs-are-invertible f e)

EX-equivs-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → is-equiv f → g ∼ f → is-equiv g
EX-equivs-closed-under-∼ {f = f} {g = g} e i = EX-joyal-equivs-are-equivs g
  (EX-retractions-closed-under-∼ f g s i , EX-sections-closed-under-∼ f g r i) where
    s = equivs-have-sections f e
    r = equivs-have-retractions f e

EX-equiv-to-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → is-singleton X → is-singleton Y
EX-equiv-to-singleton {X = X} {Y = Y} (f , e) (x , i) = (f x , T) where
  T : (y : Y) → f x ＝ y
  T y =
    f x               ＝⟨ ap f (i (inverse f e y)) ⟩ 
    f (inverse f e y) ＝⟨ inverses-are-sections f e y ⟩
    y                  ∎

EX-subtypes-of-sets-are-sets : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y) → left-cancellable m → is-set Y → is-set X
EX-subtypes-of-sets-are-sets m i s x = Hedberg x A where
  A : (x' : domain m) → wconstant-endomap (x ＝ x')
  A x' = i ∘ (ap m) , (λ p p' → ap i (s (m x) (m x') (ap m p) (ap m p')))

EX-pr₁-lc : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ((x : X) → is-subsingleton (A x)) → left-cancellable (λ (t : Σ A) → pr₁ t)
EX-pr₁-lc s p = to-Σ-＝ (p , s _ _ _)

EX-subsets-of-sets-are-sets : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) → is-set X → ((x : X) → is-subsingleton (A x))
                              → is-set (Σ x ꞉ X , A x)
EX-subsets-of-sets-are-sets x A s i = EX-subtypes-of-sets-are-sets pr₁ (pr₁-lc i) s

EX-to-subtype-＝ : {X : 𝓦 ̇ } {A : X → 𝓥 ̇ } {x y : X} {a : A x} {b : A y}
                   → ((x : X) → is-subsingleton (A x)) → x ＝ y → (x , a) ＝ (y , b)
EX-to-subtype-＝ C p = to-Σ-＝ (p , C (rhs p) _ _)

EX-pr₁-is-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ((x : X) → is-singleton (A x)) → is-equiv (λ (t : Σ A) → pr₁ t)
EX-pr₁-is-equiv {A = A} S = invertibles-are-equivs pr₁
  ((λ t → (t , center (A t) (S t))) , (λ s → to-Σ-＝ (refl (pr₁ s) ,  centrality (A (pr₁ s)) (S (pr₁ s)) (pr₂ s))) , refl)

EX-pr₁-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ((x : X) → is-singleton (A x)) → Σ A ≃ X
EX-pr₁-≃ i = pr₁ , pr₁-is-equiv i

EX-ΠΣ-distr-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
                → (Π x ꞉ X , Σ a ꞉ A x , P x a) ≃ (Σ f ꞉ Π A , Π x ꞉ X , P x (f x))
EX-ΠΣ-distr-≃ {𝓤} {𝓥} {𝓦} {X} {A} {P} = invertibility-gives-≃ F (G , refl , refl) where
  F : (Π x ꞉ X , Σ a ꞉ A x , P x a) → (Σ f ꞉ Π A , Π x ꞉ X , P x (f x))
  F f = (λ x → pr₁ (f x)) , (λ x → pr₂ (f x))

  G : (Σ f ꞉ Π A , Π x ꞉ X , P x (f x)) → (Π x ꞉ X , Σ a ꞉ A x , P x a)
  G y = λ x → ((pr₁ y) x , (pr₂ y) x)

EX-Σ-assoc : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : Σ Y → 𝓦 ̇ } → Σ Z ≃ (Σ x ꞉ X , Σ y ꞉ Y x , Z (x , y))
EX-Σ-assoc {𝓤} {𝓥} {𝓦} {X} {Y} {Z} = invertibility-gives-≃ F (G , refl , refl)  where
  F : Σ Z → (Σ x ꞉ X , Σ y ꞉ Y x , Z (x , y))
  F s = pr₁ (pr₁ s) , pr₂ (pr₁ s) , pr₂ s

  G : (Σ x ꞉ X , Σ y ꞉ Y x , Z (x , y)) → Σ Z
  G s = (pr₁ s , pr₁ (pr₂ s)) , pr₂ (pr₂ s)

EX-⁻¹-≃ : {X : 𝓤 ̇ } (x y : X) → (x ＝ y) ≃ (y ＝ x)
EX-⁻¹-≃ x y = _⁻¹ , invertibles-are-equivs _⁻¹ (_⁻¹ , ⁻¹-involutive , ⁻¹-involutive)

EX-singleton-types-≃ : {X : 𝓤 ̇ } (x : X) → singleton-type' x ≃ singleton-type x
EX-singleton-types-≃ x = Σ-cong (EX-⁻¹-≃ x)

EX-singletons-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → is-singleton X → is-singleton Y → X ≃ Y
EX-singletons-≃ (c , C) (d , D) = invertibility-gives-≃ (λ _ → d) ((λ _ → c) , C , D)

EX-maps-of-singletons-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-singleton X → is-singleton Y → is-equiv f
EX-maps-of-singletons-are-equivs f (c , C) (_ , D) = invertibles-are-equivs f ((λ _ → c) , C , (λ x → D (f c) ⁻¹ ∙ D x))

EX-logically-equivalent-subsingletons-are-equivalent : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → is-subsingleton X → is-subsingleton Y
                                                       → X ⇔ Y → X ≃ Y
EX-logically-equivalent-subsingletons-are-equivalent X Y u v (f , g) =
  invertibility-gives-≃ f (g , (λ x → u _ x) , (λ x → v _ x))

EX-singletons-are-equivalent : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → is-singleton X → is-singleton Y → X ≃ Y
EX-singletons-are-equivalent X Y = EX-singletons-≃

EX-NatΣ-fiber-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (φ : Nat A B) (x : X) (b : B x)
                       → fiber (φ x) b ≃ fiber (NatΣ φ) (x , b)
EX-NatΣ-fiber-equiv A B φ x b = ≃-sym
  ((fiber (NatΣ φ) (x , b))                                                ≃⟨ Σ-cong (λ (ξ , α) → Σ-＝-≃ (ξ , φ ξ α) (x , b)) ⟩
   (Σ (x' , a') ꞉ (Σ A) , (Σ p ꞉ (x' ＝ x) , transport B p (φ x' a') ＝ b))             ≃⟨ EX-Σ-assoc ⟩
   (Σ x' ꞉ _ , (Σ a' ꞉ (A x') , (Σ p ꞉ (x' ＝ x) , transport B p (φ x' a') ＝ b)))      ≃⟨ Σ-cong (λ _ → Σ-flip) ⟩
   (Σ x' ꞉ _ , (Σ p ꞉ (x' ＝ x) , (Σ a' ꞉ (A x') , transport B p (φ x' a') ＝ b)))      ≃⟨ ≃-sym EX-Σ-assoc ⟩
   (Σ (x' , p) ꞉ (singleton-type x) , (Σ a' ꞉ (A x') , transport B p (φ x' a') ＝ b))   ≃⟨ ≃-sym (F , E) ⟩
   (fiber (φ x) b)                                                                      ■)  where

  F : fiber (φ x) b → (Σ (x' , p) ꞉ (singleton-type x) , (Σ a' ꞉ A x' , transport B p (φ x' a') ＝ b))
  F (a , r) = ((x , refl x) , (a , r))

  E : (η : (Σ (x' , p) ꞉ (singleton-type x) , (Σ a' ꞉ A x' , transport B p (φ x' a') ＝ b))) → is-singleton (fiber F η)
  E ((x , refl x) , (a , r)) = (((a , r) , refl ((x , refl x) , (a , r))) , (λ ((α , ρ) , q) → to-Σ-＝ ((e₀ ((α , ρ) , q)) , e₁ ((α , ρ) , q)))) where
    S : is-set (singleton-type x)
    S = singletons-are-sets (singleton-type x) (singleton-types-are-singletons _ x)

    e₀ : (((α , ρ) , q) : fiber F ((x , refl x) , (a , r))) → (a , r) ＝ (α , ρ)
    e₀ ((α , ρ) , q) = transport (λ Q → transport (λ (ξ , π) → Σ a ꞉ A ξ , transport B π (φ ξ a) ＝ b) Q (α , ρ) ＝ (a , r)) (S (x , refl x) (x , refl x) (pr₁ (from-Σ-＝ q)) (refl (x , refl x))) (pr₂ (from-Σ-＝ q)) ⁻¹

    e₁ : (((α , ρ) , q) : fiber F ((x , refl x) , (a , r))) → transport _ (e₀ ((α , ρ) , q)) (refl ((x , refl x) , (a , r))) ＝ q
    e₁ ((a , r) , (refl ((x , refl x) , (a , r)))) = refl (refl ((x , refl x) , (a , r)))

EX-NatΣ-fiber-equiv' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (φ : Nat A B) (x : X) (b : B x)
                       → fiber (φ x) b ≃ fiber (NatΣ φ) (x , b)
EX-NatΣ-fiber-equiv' A B φ x b = F , invertibles-are-equivs F (G , γ , ϕ) where
  F : fiber (φ x) b → fiber (NatΣ φ) (x , b)
  F (a , refl _) = (x , a) , refl _

  G : fiber (NatΣ φ) (x , b) → fiber (φ x) b
  G ((x , a) , refl _) = a , refl _

  ϕ : F ∘ G ∼ id
  ϕ (_ , refl _) = refl _

  γ : G ∘ F ∼ id
  γ (_ , refl _) = refl _

EX-NatΣ-equiv-gives-fiberwise-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } (φ : Nat A B) → is-equiv (NatΣ φ)
                                      → ((x : X) → is-equiv (φ x))
EX-NatΣ-equiv-gives-fiberwise-equiv φ E x b = EX-equiv-to-singleton (≃-sym (EX-NatΣ-fiber-equiv _ _ φ x b)) (E (x , b))

EX-Σ-is-subsingleton : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → is-subsingleton X → ((x : X) → is-subsingleton (A x)) → is-subsingleton (Σ A)
EX-Σ-is-subsingleton S F (x , a) (x' , a') = to-Σ-＝ (S x x' , (F x') (transport _ (S x x') a) a')

EX-×-is-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → is-singleton X → is-singleton Y → is-singleton (X × Y)
EX-×-is-singleton (c , f) (d , g) = (c , d) , (λ (x' , y') → to-×-＝ (f x' , g y'))

EX-×-is-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → is-subsingleton X → is-subsingleton Y → is-subsingleton (X × Y)
EX-×-is-subsingleton F G (x , y) (x' , y') = to-×-＝ (F x x' , G y y')

EX-×-is-subsingleton' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → ((Y → is-subsingleton X) × (X → is-subsingleton Y)) → is-subsingleton (X × Y)
EX-×-is-subsingleton' (F , G) (x , y) (x' , y') = to-×-＝ (F y x x' , G x y y')

EX-×-is-subsingleton'-back : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → is-subsingleton (X × Y) → (Y → is-subsingleton X) × (X → is-subsingleton Y)
EX-×-is-subsingleton'-back F =
  (λ y x x' → pr₁ (from-×-＝ (F (x , y) (x' , y)))) , (λ x y y' → pr₂ (from-×-＝ (F (x , y) (x , y'))))

EX-ap₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x x' : X} {y y' : Y} → x ＝ x' → y ＝ y' → f x y ＝ f x' y'
EX-ap₂ _ (refl _) (refl _) = refl _



-- prove that function extensionality and f being an equivalence implies (_∘ f) is an equivalence
--

precomp-of-equiv-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → (fe : funext 𝓥 𝓦) → (fe' : funext 𝓤 𝓦)
                            → (f : X → Y) → is-equiv f → is-equiv (_∘ f)
precomp-of-equiv-is-equiv {Z = Z} fe fe' f E = invertibles-are-equivs (_∘ f) (G , (λ h → fe (ϕ h)) , (λ h → fe' (γ h))) where
  G : (h : domain f → Z) → codomain f → Z
  G h = h ∘ (inverse f E)

  ϕ : (h : codomain f → Z) → (y : codomain f) → (G (h ∘ f)) y ＝ h y
  ϕ h y = ap h (inverses-are-sections f E y)

  γ : (h : domain f → Z) → (x : domain f) → ((G h) ∘ f) x ＝ h x
  γ h x = ap h (inverses-are-retractions f E x)



-- give a fiberwise involutive equivalence (mirror: (n : ℕ) → Fin n → Fin n) that is not the identity
--

module EX-finite-types (ua : Univalence) where
  hfe : hfunext 𝓤₀ 𝓤₁
  hfe = univalence-gives-global-hfunext ua

  fin : ∃! Fin' ꞉ (ℕ → 𝓤₀ ̇ ) , (Fin' 0 ＝ 𝟘) × ((n : ℕ) → Fin' (succ n) ＝ Fin' n + 𝟙)
  fin = finite-types.fin hfe

  Fin : ℕ → 𝓤₀ ̇
  Fin = pr₁ (pr₁ fin)

  plusOne : (n : ℕ) → Fin n → Fin (succ n)
  plusOne 0 _ = inr ⋆
  plusOne (succ n) (inr ⋆) = inr ⋆
  plusOne (succ n) (inl μ) = inl (plusOne n μ)

  mirror : (n : ℕ) → Fin n → Fin n
  mirror 0 = id
  mirror 1 = id
  mirror (succ (succ n)) (inr ⋆) = inl (mirror (succ n) (inr ⋆))
  mirror (succ (succ n)) (inl μ) = plusOne (succ n) (mirror (succ n) μ)

  plusMirror : (n : ℕ) → (plusOne n) ∘ (mirror n) ∼ (mirror (succ n)) ∘ inl
  plusMirror (succ n) (inr ⋆) = refl _
  plusMirror (succ n) (inl μ) = refl _

  mirrorPlus : (n : ℕ) → (mirror (succ n)) ∘ (plusOne n) ∼ inl ∘ (mirror n)
  mirrorPlus (succ n) (inr ⋆) = refl _
  mirrorPlus (succ n) (inl μ) = (ap (plusOne (succ n)) (mirrorPlus n μ)) ∙ (ap inl (plusMirror n μ))

  mirror-is-involution : (n : ℕ) → (mirror n) ∘ (mirror n) ∼ id
  mirror-is-involution 0 _ = refl _
  mirror-is-involution 1 _ = refl _
  mirror-is-involution (succ (succ n)) (inr ⋆) = ap (plusOne (succ n)) (mirror-is-involution (succ n) (inr ⋆))
  mirror-is-involution (succ (succ n)) (inl μ) = mirrorPlus (succ n) (mirror (succ n) μ) ∙ ap inl (mirror-is-involution (succ n) μ)

  mirror-equiv : (n : ℕ) → Fin n ≃ Fin n
  mirror-equiv n = mirror n , invertibles-are-equivs (mirror n) (mirror n , mirror-is-involution n , mirror-is-involution n)

  Mirror : Fin ＝ Fin
  Mirror = hfunext-gives-dfunext hfe (λ n → Eq→Id (ua _) _ _ (mirror-equiv n))

  Mirror-is-not-refl : Mirror ≠ refl Fin
  Mirror-is-not-refl z = inl-inr-disjoint-images ((s ∙ t) ⁻¹ ∙ ap (λ x → (Id→fun x) (inr ⋆)) (ap (ap (λ - → - 2)) z)) where
    F : Fin ∼ Fin
    F n = Eq→Id (ua _) _ _ (mirror-equiv n)

    s : Id→fun (happly Fin Fin (inverse (happly Fin Fin) (hfe Fin Fin) F) 2)
          (inr ⋆) ＝ Id→fun (Eq→Id (ua _) _ _ (mirror-equiv 2)) (inr ⋆)
    s = ap (λ - → Id→fun (- 2) (inr ⋆)) (inverses-are-sections (happly Fin Fin) (hfe Fin Fin) F)

    t : Id→fun (Eq→Id (ua _) _ _ (mirror-equiv 2)) (inr ⋆) ＝ inl (inr ⋆)
    t = ap (λ - → (pr₁ -) (inr ⋆)) (inverses-are-sections (Id→Eq _ _) (ua _ _ _) (mirror-equiv 2))

  -- which  equality (Fin ＝ Fin')  does the universal property of Fin give?

  fin' : ∃! Fin' ꞉ (ℕ → 𝓤₀ ̇ ) , (Fin' 0 ＝ 𝟘) × ((n : ℕ) → Fin' (succ n) ＝ 𝟙 + Fin' n)
  fin' = ℕ-is-nno hfe (𝓤₀ ̇ ) 𝟘 (𝟙 +_)

  Fin' : ℕ → 𝓤₀ ̇
  Fin' = pr₁ (center _ fin')

  naive-Fin-＝-Fin' : Fin ＝ Fin'
  naive-Fin-＝-Fin' = (univalence-gives-funext (ua _)) (λ n → Eq→Id (ua _) (Fin n) (Fin' n) (f n , e n)) where
    f : (n : ℕ) → Fin n → Fin' n
    f 0 = id
    f (succ n) (inr ⋆) = inl ⋆
    f (succ n) (inl μ) = inr (f n μ)

    g : (n : ℕ) → Fin' n → Fin n
    g 0 = id
    g (succ n) (inl ⋆) = inr ⋆
    g (succ n) (inr μ) = inl (g n μ)

    u : (n : ℕ) → (g n) ∘ (f n) ∼ id
    u 0 _ = refl _
    u (succ n) (inr ⋆) = refl (inr ⋆)
    u (succ n) (inl μ) = ap inl (u n μ)

    v : (n : ℕ) → (f n) ∘ (g n) ∼ id
    v 0 _ = refl _
    v (succ n) (inl ⋆) = refl (inl ⋆)
    v (succ n) (inr μ) = ap inr (v n μ)

    e : (n : ℕ) → is-equiv (f n)
    e n = invertibles-are-equivs (f n) (g n , u n , v n)

  +-𝟙-comm : (n : ℕ) → 𝟙 + (Fin' n) ≃ (Fin' n) + 𝟙
  +-𝟙-comm n = (f n) , (e n) where
    f : (n : ℕ) → 𝟙 + (Fin' n) → (Fin' n) + 𝟙
    f n (inl ⋆) = inr ⋆
    f n (inr μ) = inl μ

    g : (n : ℕ) → (Fin' n) + 𝟙 → 𝟙 + (Fin' n)
    g n (inr ⋆) = inl ⋆
    g n (inl μ) = inr μ

    e : (n : ℕ) → is-equiv (f n)
    e n = invertibles-are-equivs (f n) (g n , u n , v n) where
      u : (n : ℕ) → (g n) ∘ (f n) ∼ id
      u n (inl ⋆) = refl (inl ⋆)
      u n (inr μ) = refl (inr μ)

      v : (n : ℕ) → (f n) ∘ (g n) ∼ id
      v n (inr ⋆) = refl (inr ⋆)
      v n (inl μ) = refl (inl μ)

  universal-Fin-＝-Fin' : Fin ＝ Fin'
  universal-Fin-＝-Fin' = pr₁ (from-Σ-＝ ((pr₂ fin) (Fin' , refl 𝟘 , (λ n → Eq→Id (ua _) _ _ (+-𝟙-comm n)))))
{-
  naive-Fin-＝-Fin'-is-universal : naive-Fin-＝-Fin' ＝ universal-Fin-＝-Fin'
  naive-Fin-＝-Fin'-is-universal = (inverses-are-retractions F (pr₂ E) naive-Fin-＝-Fin') ⁻¹ ∙ ap G P ∙ inverses-are-retractions F (pr₂ E) universal-Fin-＝-Fin' where
    E : (Fin ＝ Fin') ≃ (Fin ∼ Fin')
    E = hfunext-≃ (univalence-gives-global-hfunext ua) Fin Fin'
    F : Fin ＝ Fin' → Fin ∼ Fin'
    F = ⌜ E ⌝
    G : Fin ∼ Fin' → Fin ＝ Fin'
    G = inverse ⌜ E ⌝ (pr₂ E)
    U : Fin ∼ Fin'
    U = F universal-Fin-＝-Fin'
    N : Fin ∼ Fin'
    N = F naive-Fin-＝-Fin'
    P : N ＝ U
    P = (univalence-gives-global-dfunext ua) (λ n → (inverses-are-retractions (FF n) (pr₂ (EE n)) (u n)) ⁻¹ ∙ ap (GG n) (PP n) ∙ inverses-are-retractions (FF n) (pr₂ (EE n)) (v n)) where
      u : (n : ℕ) → Fin n ＝ Fin' n
      u n = (⌜ hfunext-≃ (univalence-gives-global-hfunext ua) Fin Fin' ⌝ naive-Fin-＝-Fin') n
      v : (n : ℕ) → Fin n ＝ Fin' n
      v n = (⌜ hfunext-≃ (univalence-gives-global-hfunext ua) Fin Fin' ⌝ universal-Fin-＝-Fin') n
      EE : (n : ℕ) → (Fin n ＝ Fin' n) ≃ (Fin n ≃ Fin' n)
      EE n = Id→Eq _ _ , ua _ _ _
      FF : (n : ℕ) → Fin n ＝ Fin' n → Fin n ≃ Fin' n
      FF n = ⌜ EE n ⌝
      GG : (n : ℕ) → Fin n ≃ Fin' n → Fin n ＝ Fin' n
      GG n = inverse ⌜ EE n ⌝ (pr₂ (EE n))
      NN : (n : ℕ) → Fin n ≃ Fin' n
      NN n = (FF n) (u n)
      UU : (n : ℕ) → Fin n ≃ Fin' n
      UU n = (FF n) (v n)
      PP : (n : ℕ) → (NN n) ＝ (UU n)
      PP n = feq-to-eeq ((univalence-gives-global-dfunext ua) (Q n)) where
        feq-to-eeq : {f g : Fin n ≃ Fin' n} → ⌜ f ⌝ ＝ ⌜ g ⌝ → f ＝ g
        feq-to-eeq = {!!}

        Q : (n : ℕ) → (μ : Fin n) →  ⌜ NN n ⌝ μ ＝ ⌜ UU n ⌝ μ
        Q 1 (inr ⋆) = {!!}
        Q (succ (succ n)) (inr ⋆) = {!!}
        Q (succ (succ n)) (inl ν) = {!!}
-}

--  Id→fun ((⌜ hfunext-≃ (univalence-gives-global-hfunext ua) Fin Fin' ⌝ naive-Fin-＝-Fin') n)


-- (⌜ hfunext-≃ (univalence-gives-global-hfunext ua) Fin Fin' ⌝ naive-Fin-＝-Fin') n : Fin n ＝ Fin' n
-- (⌜ hfunext-≃ (univalence-gives-global-hfunext ua) Fin Fin' ⌝ universal-Fin-＝-Fin') n : Fin n ＝ Fin' n

-- (Fin n ＝ Fin' n) ≃ (Fin n ≃ Fin' n)

-- equality of equivalences is just equality of the underlying functions

-- get the equality of the underlying (Fin n → Fin' n) functions using funext

-- extend to equality of equivalences

-- apply the inverse of the univalence equivalence to get back to Fin n ＝ Fin' n





-- naive-Fin-＝-Fin' : Fin ＝ Fin'

-- (Fin ＝ Fin') ≃ (Fin ∼ Fin')

-- construct (universal-Fin-∼-Fin' ＝ naive-Fin-∼-Fin' using dfunext)

-- apply the inverse to transport equality into (Fin ＝ Fin')






  -- prove that (Fin n) is a set

  inl-is-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x x' : X} → inl {Y = Y} x ＝ inl x' → x ＝ x'
  inl-is-lc (refl (inl a)) = refl a

  Fin-has-decidable-equality : (n : ℕ) →  has-decidable-equality (Fin n)
  Fin-has-decidable-equality (succ n) (inr ⋆) (inr ⋆) = inl (refl (inr ⋆))
  Fin-has-decidable-equality (succ n) (inr ⋆) (inl _) = inr (≠-sym inl-inr-disjoint-images)
  Fin-has-decidable-equality (succ n) (inl _) (inr ⋆) = inr inl-inr-disjoint-images
  Fin-has-decidable-equality (succ n) (inl μ) (inl ν) = +-recursion (inl ∘ (ap inl)) (λ z → inr (z ∘ inl-is-lc)) (Fin-has-decidable-equality n μ ν)

  Fin-is-set : (n : ℕ) → is-set (Fin n)
  Fin-is-set n = hedberg (Fin-has-decidable-equality n)


  -- prove that Fin is left cancellable but not an embedding

  -- Fin-is-lc (succ n) (succ m) : Fin (succ n) ＝ Fin (succ m) → succ n ＝ succ m

  lemma₀ : {A : 𝓤 ̇ } → (s : A + (¬ A)) → A → Σ a ꞉ A , s ＝ inl a
  lemma₀ (inl a) _ = a , refl _
  lemma₀ (inr z) a = !𝟘 _ (z a)

  lemma₂ : (n : ℕ) → (μ : Fin n) → Σ p ꞉ μ ＝ μ , Fin-has-decidable-equality n μ μ ＝ inl p
  lemma₂ n μ = lemma₀ (Fin-has-decidable-equality n μ μ) (refl μ)

  lemma₃ : (n : ℕ) → (μ : Fin (succ n)) → μ ≠ inr ⋆ → Σ ν ꞉ Fin n , μ ＝ inl ν
  lemma₃ n (inr ⋆) z = !𝟘 _ (z (refl (inr ⋆)))
  lemma₃ (succ n) (inl ν) _ = ν , refl (inl ν)

  ⌜⌝-hom : {A B C : 𝓤 ̇ } (E : A ≃ B) (F : B ≃ C) → ⌜ E ● F ⌝ ∼ ⌜ F ⌝ ∘ ⌜ E ⌝
  ⌜⌝-hom {A = A} {B = B} {C = C} E = ℍ-≃ (ua _) B (λ Y Q → ⌜ E ● Q ⌝ ∼ ⌜ Q ⌝ ∘ ⌜ E ⌝) (λ x → ap (λ - → ⌜ - ⌝ x) id-≃-right) C where
    id-≃-right : E ● (id-≃ B) ＝ E
    id-≃-right = ℍ-≃ (ua _) A (λ Y Q → Q ● (id-≃ Y) ＝ Q) (id-≃-left dfe dfe' (id-≃ A)) B E where
      dfe = univalence-gives-dfunext (ua _)
      dfe' = univalence-gives-dfunext (ua _)

  swap : (n : ℕ) → Fin n → Fin (succ n) ≃ Fin (succ n)
  swap n μ = F , E where
    F : Fin (succ n) → Fin (succ n)
    F (inr ⋆) = inl μ
    F (inl ν) = +-recursion (λ _ → inr ⋆) (λ _ → inl ν) (Fin-has-decidable-equality n μ ν)

    E : is-equiv F
    E = invertibles-are-equivs F (F , u , u) where
      u : (ν : Fin (succ n)) → F (F ν) ＝ ν
      u (inr ⋆) = transport (λ - → +-recursion (λ _ → inr ⋆) (λ _ → inl μ) - ＝ inr ⋆) ((pr₂ (lemma₂ n μ)) ⁻¹) (refl (inr ⋆))
      u (inl ν) = +-recursion A (λ z → ap F (u' z D) ∙ (u' z D)) D where
        D : (μ ＝ ν) + (μ ≠ ν)
        D = Fin-has-decidable-equality n μ ν
        u' : μ ≠ ν → (s : (μ ＝ ν) + (μ ≠ ν)) → +-recursion (λ _ → inr ⋆) (λ _ → inl ν) s ＝ inl ν
        u' z (inl p) = !𝟘 _ (z p)
        u' z (inr _) = refl _
        A : μ ＝ ν → F (+-recursion (λ _ → inr ⋆) (λ _ → inl ν) D) ＝ inl ν
        A p = ap F a ∙ ap inl p where
          a : +-recursion (λ _ → inr ⋆) (λ _ → inl ν) D ＝ inr ⋆
          a = (ap (λ x → +-recursion (λ _ → inr ⋆) (λ _ → inl ν) (Fin-has-decidable-equality n μ x)) (p ⁻¹)) ∙ ap (λ - → +-recursion (λ _ → inr ⋆) (λ _ → inl ν) -) (pr₂ (lemma₂ n μ))

  fix-inr : (n m : ℕ) → Fin (succ n) ≃ Fin (succ m) → Σ F ꞉ (Fin (succ n) ≃ Fin (succ m)) , ⌜ F ⌝ (inr ⋆) ＝ inr ⋆
  fix-inr n m E = +-recursion (λ p → E , p) A D where
    D : ((⌜ E ⌝ (inr ⋆)) ＝ inr ⋆) + ((⌜ E ⌝ (inr ⋆)) ≠ inr ⋆)
    D = Fin-has-decidable-equality (succ m) (⌜ E ⌝ (inr ⋆)) (inr ⋆)

    A : ⌜ E ⌝ (inr ⋆) ≠ inr ⋆ → Σ F ꞉ (Fin (succ n) ≃ Fin (succ m)) , ⌜ F ⌝ (inr ⋆) ＝ inr ⋆
    A z = ((swap n X) ● E) , (W ∙ Z) where
      zz :  ⌜ ≃-sym E ⌝ (inr ⋆) ≠ inr ⋆
      zz q = z ((((inverses-are-sections (pr₁ E) (pr₂ E) (inr ⋆)) ⁻¹) ∙ ap (pr₁ E) q) ⁻¹)

      X : Fin n
      X = pr₁ (lemma₃ n (⌜ ≃-sym E ⌝ (inr ⋆)) zz)

      Y : inl (pr₁ (lemma₃ n (⌜ ≃-sym E ⌝ (inr ⋆)) zz)) ＝ ⌜ ≃-sym E ⌝ (inr ⋆)
      Y = y n (⌜ ≃-sym E ⌝ (inr ⋆)) zz where
        y : (n : ℕ) → (μ : Fin (succ n)) → (z : μ ≠ inr ⋆) → inl (pr₁ (lemma₃ n μ z)) ＝ μ
        y n (inr ⋆) z = !𝟘 _ (z (refl (inr ⋆)))
        y (succ n) (inl μ) _ = refl _

      W : ⌜ (swap n X) ● E ⌝ (inr ⋆) ＝ (pr₁ E) (inl X)
      W = ⌜⌝-hom (swap n X) E (inr ⋆)

      Z : (pr₁ E) (inl X) ＝ inr ⋆
      Z = ap (pr₁ E) Y ∙ (inverses-are-sections (pr₁ E) (pr₂ E) (inr ⋆))

  Fin-is-lc : (n m : ℕ) → Fin n ＝ Fin m → n ＝ m
  Fin-is-lc 0 0 _ = refl 0
  Fin-is-lc (succ n) 0 p = !𝟘 _ (Id→fun p (inr ⋆))
  Fin-is-lc 0 (succ n) p = !𝟘 _ (Id→fun (p ⁻¹) (inr ⋆))
  Fin-is-lc (succ n) (succ m) p = ap succ (Fin-is-lc n m (F n m p)) where
    F : (n m : ℕ) → Fin (succ n) ＝ Fin (succ m) → Fin n ＝ Fin m
    F 0 0 _ = ap Fin (refl 0)
    F 0 (succ n) q = !𝟘 _ (inl-inr-disjoint-images t) where
      ϕ : Fin 1 ≃ Fin (succ (succ n))
      ϕ = Id→Eq _ _ q

      f : (μ : Fin 1) → μ ＝ inr ⋆
      f (inr ⋆) = refl (inr ⋆)

      r : (pr₁ ϕ) ((inverse (pr₁ ϕ) (pr₂ ϕ)) (inl (inr ⋆))) ＝ (pr₁ ϕ) (inr ⋆)
      r = ap (pr₁ ϕ) (f ((inverse (pr₁ ϕ) (pr₂ ϕ)) (inl (inr ⋆))))

      s : (pr₁ ϕ) (inr ⋆) ＝ (pr₁ ϕ) ((inverse (pr₁ ϕ) (pr₂ ϕ)) (inr ⋆))
      s = ap (pr₁ ϕ) (f ((inverse (pr₁ ϕ) (pr₂ ϕ)) (inr ⋆)) ⁻¹)

      t : inl (inr ⋆) ＝ inr ⋆
      t = inverses-are-sections (pr₁ ϕ) (pr₂ ϕ) (inl (inr ⋆)) ⁻¹ ∙ r ∙ s ∙ inverses-are-sections (pr₁ ϕ) (pr₂ ϕ) (inr ⋆)

    F (succ n) 0 q = (F 0 (succ n) (q ⁻¹)) ⁻¹
    F (succ n) (succ m) q = Eq→Id (ua _) _ _ (g , E) where
      ϕ : Fin (succ (succ n)) ≃ Fin (succ (succ m))
      ϕ = pr₁ (fix-inr (succ n) (succ m) (Id→Eq _ _ q))

      ψ : Fin (succ (succ m)) → Fin (succ (succ n))
      ψ = inverse (pr₁ ϕ) (pr₂ ϕ)

      γ : ⌜ ϕ ⌝ (inr ⋆) ＝ inr ⋆
      γ = pr₂ (fix-inr (succ n) (succ m) (Id→Eq _ _ q))

      γ' : inverse ⌜ ϕ ⌝ (pr₂ ϕ) (inr ⋆) ＝ inr ⋆
      γ' = ((inverses-are-retractions ⌜ ϕ ⌝ (pr₂ ϕ) (inr ⋆)) ⁻¹ ∙ ap (inverse ⌜ ϕ ⌝ (pr₂ ϕ)) γ) ⁻¹

      Λ₁ : Fin (succ (succ n)) → Fin (succ n)
      Λ₁ (inr ⋆) = inr ⋆
      Λ₁ (inl μ) = μ

      Λ₂ : Fin (succ (succ m)) → Fin (succ m)
      Λ₂ (inr ⋆) = inr ⋆
      Λ₂ (inl μ) = μ

      g : Fin (succ n) → Fin (succ m)
      g = Λ₂ ∘ ⌜ ϕ ⌝ ∘ inl

      h : Fin (succ m) → Fin (succ n)
      h = Λ₁ ∘ ψ ∘ inl

      U : (μ : Fin (succ n)) → Σ ν ꞉ (Fin (succ m)) , ⌜ ϕ ⌝ (inl μ) ＝ inl ν
      U μ = lemma₃ (succ m) (⌜ ϕ ⌝ (inl μ)) (λ p → inl-inr-disjoint-images ((inverses-are-retractions ⌜ ϕ ⌝ (pr₂ ϕ) _ ⁻¹) ∙ ap ψ (p ∙ γ ⁻¹) ∙ (inverses-are-retractions ⌜ ϕ ⌝ (pr₂ ϕ) _)))

      V : (ν : Fin (succ m)) → Σ μ ꞉ (Fin (succ n)) , ψ (inl ν) ＝ inl μ
      V ν = lemma₃ (succ n) (ψ (inl ν)) (λ p → inl-inr-disjoint-images ((inverses-are-sections ⌜ ϕ ⌝ (pr₂ ϕ) _ ⁻¹) ∙ ap ⌜ ϕ ⌝ (p ∙ γ' ⁻¹) ∙ (inverses-are-sections ⌜ ϕ ⌝ (pr₂ ϕ) _)))

      E : is-equiv g
      E = invertibles-are-equivs g (h , A , B) where
        A : Λ₁ ∘ ψ ∘ inl ∘ Λ₂ ∘ ⌜ ϕ ⌝ ∘ inl ∼ id
        A μ = (ap Λ₁ r ∙ ap (Λ₁ ∘ ψ ∘ inl ∘ Λ₂) (pr₂ (U μ)) ⁻¹) ⁻¹ where
          r : inl μ ＝ ψ (inl (pr₁ (U μ)))
          r = inverses-are-retractions ⌜ ϕ ⌝ (pr₂ ϕ) (inl μ) ⁻¹ ∙ ap ψ (pr₂ (U μ))

        B : Λ₂ ∘ ⌜ ϕ ⌝ ∘ inl ∘ Λ₁ ∘ ψ ∘ inl ∼ id
        B ν = (ap Λ₂ r ∙ ap (Λ₂ ∘ ⌜ ϕ ⌝ ∘ inl ∘ Λ₁) (pr₂ (V ν)) ⁻¹) ⁻¹ where
          r : inl ν ＝ ⌜ ϕ ⌝ (inl (pr₁ (V ν)))
          r = inverses-are-sections ⌜ ϕ ⌝ (pr₂ ϕ) (inl ν) ⁻¹ ∙ ap ⌜ ϕ ⌝ (pr₂ (V ν))

  Fin-is-not-embedding : ¬(is-embedding Fin)
  Fin-is-not-embedding B = inl-inr-disjoint-images ((ap (λ - → Id→fun - (inr ⋆)) b ∙ t) ⁻¹) where
    A : Σ q ꞉ 2 ＝ 2 , transport (λ - → Fin - ＝ Fin 2) q (refl (Fin 2)) ＝ Eq→Id (ua _) _ _ (mirror-equiv 2)
    A = from-Σ-＝ ((B (Fin 2)) (2 , refl (Fin 2)) (2 , Eq→Id (ua _) _ _ (mirror-equiv 2)))

    a : pr₁ A ＝ refl 2
    a = ℕ-is-set 2 2 _ _

    b : refl (Fin 2) ＝ Eq→Id (ua _) _ _ (mirror-equiv 2)
    b = transport (λ - → transport _ - (refl (Fin 2)) ＝ Eq→Id (ua _) _ _ (mirror-equiv 2)) a (pr₂ A)
    
    t : Id→fun (Eq→Id (ua _) _ _ (mirror-equiv 2)) (inr ⋆) ＝ inl (inr ⋆)
    t = ap (λ - → (pr₁ -) (inr ⋆)) (inverses-are-sections (Id→Eq _ _) (ua _ _ _) (mirror-equiv 2))


  -- finite symmetric groups

  Fin-≃-is-set : (n : ℕ) → is-set (Fin n ≃ Fin n)
  Fin-≃-is-set n e f = equiv-to-subsingleton (Σ-＝-≃ e f) X  where
      dfe = univalence-gives-dfunext (ua _)
      Q : (⌜ e ⌝ ＝ ⌜ f ⌝) ≃  (⌜ e ⌝ ∼ ⌜ f ⌝) 
      Q = hfunext-≃ (univalence-gives-hfunext (ua _)) ⌜ e ⌝ ⌜ f ⌝
      R : is-subsingleton (⌜ e ⌝ ∼ ⌜ f ⌝)
      R = Π-is-subsingleton dfe (λ x → Fin-is-set n _ _)
      X : is-subsingleton (Σ ρ ꞉ (⌜ e ⌝ ＝ ⌜ f ⌝) , transport is-equiv ρ (pr₂ e) ＝ pr₂ f)
      X = Σ-is-subsingleton (equiv-to-subsingleton Q R) (λ _ → subsingletons-are-sets (is-equiv ⌜ f ⌝) (being-equiv-is-subsingleton dfe dfe (pr₁ f)) _ _)

  id-≃-right : (n : ℕ) → (E : Fin n ≃ Fin n) → (E ● id-≃ (Fin n)) ＝ E
  id-≃-right n E = ℍ-≃ (ua _) (Fin n) (λ Y Q → Q ● (id-≃ Y) ＝ Q) (id-≃-left dfe dfe (id-≃ (Fin n))) (Fin n) E where
    dfe = univalence-gives-dfunext (ua _)

  S : (n : ℕ) → Group 𝓤₀
  S n = (((Fin n ≃ Fin n) , Fin-≃-is-set n  , _●_ , id-≃ (Fin n) , id-≃-left dfe dfe , id-≃-right n , (λ a b c → (●-assoc dfe dfe a b c ⁻¹))) , ≃-sym , ≃-sym-left-inverse dfe) where
    dfe = univalence-gives-dfunext (ua _)


-- prove that Σ and Π preserve hlevel
--

ap-equiv-is-equiv : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X → Y) → is-equiv f → (x x' : X) → is-equiv (ap f {x = x} {x' = x'})
ap-equiv-is-equiv X Y f e x x' = invertibles-are-equivs (ap f {x = x} {x' = x'}) (G x x' , E x x' , F) where
  g : Y → X
  g = inverse f e

  Z : g ∘ f ∼ id
  Z = inverses-are-retractions f e

  Z' : f ∘ g ∼ id
  Z' = inverses-are-sections f e

  G : (s s' : X) → f s ＝ f s' → s ＝ s'
  G s s' p = Z s ⁻¹ ∙ ap g p ∙ Z s'

  E : (s s' : X) → (G s s') ∘ (ap f) ∼ id
  E s s (refl s) = ap (λ - → - ∙ inverses-are-retractions f e s) refl-right ∙ ⁻¹-left∙ (inverses-are-retractions f e s)

  F : (ap f) ∘ (G x x') ∼ id
  F p = ap f (Z x ⁻¹ ∙ ap g p ∙ Z x')                  ＝⟨ ap-∙ f (Z x ⁻¹ ∙ ap g p) (Z x') ⟩
        ap f (Z x ⁻¹ ∙ ap g p) ∙ ap f (Z x')           ＝⟨ ap (λ - → - ∙ ap f (Z x')) (ap-∙ f (Z x ⁻¹) (ap g p)) ⟩
        ap f (Z x ⁻¹) ∙ ap f (ap g p) ∙ ap f (Z x')    ＝⟨ ap (λ - → ap f (Z x ⁻¹) ∙ - ∙ ap f (Z x')) (ap-∘ g f p) ⁻¹ ⟩
        ap f (Z x ⁻¹) ∙ ap (f ∘ g) p ∙ ap f (Z x')     ＝⟨ ap (λ - → ap f (Z x ⁻¹) ∙ ap (f ∘ g) p ∙ -) (half-adjoint-condition f e x') ⟩
        ap f (Z x ⁻¹) ∙ ap (f ∘ g) p ∙ Z' (f x')       ＝⟨ ap (λ - → - ∙ ap (f ∘ g) p ∙ Z' (f x')) (ap⁻¹ f (Z x) ⁻¹ ∙ ap (λ - → - ⁻¹) (half-adjoint-condition f e x)) ⟩
        Z' (f x) ⁻¹ ∙ ap (f ∘ g) p ∙ Z' (f x')         ＝⟨ ap (λ - → Z' (f x) ⁻¹ ∙ ap (f ∘ g) p ∙ -) (⁻¹-involutive (Z' (f x'))) ⁻¹ ⟩
        Z' (f x) ⁻¹ ∙ ap (f ∘ g) p ∙ (Z' (f x') ⁻¹) ⁻¹ ＝⟨ ~-naturality' id (f ∘ g) (λ - → Z' - ⁻¹) {f x} {f x'} {p} ⟩
        ap id p                                        ＝⟨ ap-id p ⟩
        p                                              ∎
{-
goal:
ap f (Z x ⁻¹ ∙ ap g p ∙ Z x') ＝ p

solution:
distribute 2
compose 1
convert 2
dni 1
ap-id 1


∙ ap-∙ f (Z x ⁻¹ ∙ ap g p) (Z x')
∙ ap (λ - → - ∙ ap f (Z x')) (ap-∙ f (Z x ⁻¹) (ap g p))
∙ ap (λ - → ap f (Z x ⁻¹) ∙ - ∙ ap f (Z x')) (ap-∘ g f p) ⁻¹
∙ ap (λ - → ap f (Z x ⁻¹) ∙ ap (f ∘ g) p ∙ -) (half-adjoint-condition f e x')
∙ ap (λ - → - ∙ ap (f ∘ g) p ∙ Z' (f x')) (ap⁻¹ f (Z x) ⁻¹ ∙ ap (λ - → - ⁻¹) (half-adjoint-condition f e x))
∙ ap (λ - → Z' (f x) ⁻¹ ∙ ap (f ∘ g) p ∙ -) (⁻¹-involutive (Z' (f x'))) ⁻¹
∙ ~-naturality' id (f ∘ g) (λ - → Z' - ⁻¹) {f x} {f x'} {p}
∙ ap-id p


-}



ap-to-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {e : is-equiv f} {x x' : X} → (x ＝ x') ≃ (f x ＝ f x')
ap-to-equiv {_} {_} {X} {Y} {f} {e} {x} {x'} = ap f , ap-equiv-is-equiv X Y f e x x'

≃-preserves-hlevel : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (E : X ≃ Y) (n : ℕ) → X is-of-hlevel n → Y is-of-hlevel n
≃-preserves-hlevel X Y E 0 h = equiv-to-singleton (≃-sym E) h
≃-preserves-hlevel X Y E (succ n) h y y' = ≃-preserves-hlevel (g y ＝ g y') (y ＝ y') P n (h (g y) (g y'))  where
  g = inverse (pr₁ E) (pr₂ E)

  P : (g y ＝ g y') ≃ (y ＝ y')
  P = ≃-sym (ap g , ap-equiv-is-equiv Y X g (inverses-are-equivs (pr₁ E) (pr₂ E)) y y')

Σ-is-hlevel : {X : 𝓤 ̇ } (P : X → 𝓥 ̇ ) (n : ℕ) → X is-of-hlevel n → ((x : X) → (P x) is-of-hlevel n) → (Σ P) is-of-hlevel n
Σ-is-hlevel P 0 (c , π) f = ((c , center (P c) (f c)) , γ) where
  γ : (μ : Σ P) → (c , center (P c) (f c)) ＝ μ
  γ (x₁ , a₁) = to-Σ-＝ (π x₁ , (centrality (P x₁) (f x₁) _ ⁻¹ ∙ centrality (P x₁) (f x₁) _)) 
Σ-is-hlevel P (succ n) h f (x₁ , a₁) (x₂ , a₂) = ≃-preserves-hlevel _ _ E n z where
  z : (Σ p ꞉ x₁ ＝ x₂ , transport P p a₁ ＝ a₂) is-of-hlevel n
  z = Σ-is-hlevel (λ p → transport P p a₁ ＝ a₂) n (h x₁ x₂) (λ p → f x₂ (transport P p a₁) a₂)

  E : (Σ p ꞉ x₁ ＝ x₂ , transport P p a₁ ＝ a₂) ≃ ((x₁ , a₁) ＝ (x₂ , a₂))
  E = ≃-sym (Σ-＝-≃ (x₁ , a₁) (x₂ , a₂))


Π-is-hlevel : {X : 𝓤 ̇ } (P : X → 𝓥 ̇ ) (ua : Univalence) (n : ℕ) → X is-of-hlevel n → ((x : X) → (P x) is-of-hlevel n) → (Π P) is-of-hlevel n
Π-is-hlevel P ua 0 (c , π) ϕ = (λ - → pr₁ (ϕ -)) , (λ f → (univalence-gives-dfunext' (ua _) (ua _)) (λ - → pr₂ (ϕ -) (f -))) 
Π-is-hlevel P ua (succ n) h ϕ f g = {!!}
