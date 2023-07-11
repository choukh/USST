---
title: 泛等结构集合论 (2) CH → LEM
zhihu-tags: Agda, 数理逻辑, 集合论
---

# 泛等结构集合论 (2) CH → LEM

> 交流Q群: 893531731  
> 本文源码: [CH→LEM.lagda.md](https://github.com/choukh/USST/blob/main/src/CH→LEM.lagda.md)  
> 高亮渲染: [CH→LEM.html](https://choukh.github.io/USST/CH→LEM.html)  

## 前言

```agda
{-# OPTIONS --cubical --safe #-}
open import Preliminary
module CH→LEM ⦃ _ : PR ⦄ where
```

```agda
Cantor-≰ : (X : Type ℓ) → ℙ X ≰ X
Cantor-≰ X (f , f-inj) = noncontradiction ∈→∉ ∉→∈
  where
  A : ℙ X
  A x = Resize $ (∀ B → f B ≡ x → x ∉ B) , isPropΠ3 λ _ _ _ → isProp⊥
  ∈→∉ : f A ∈ A → f A ∉ A
  ∈→∉ fA∈A = unresize fA∈A A refl
  ∉→∈ : f A ∉ A → f A ∈ A
  ∉→∈ fA∉A = resize λ B fB≡ → transport (f A ∉_) (f-inj (sym fB≡)) fA∉A
```

```agda
module Lemmas (X : Type ℓ) (X-set : isSet X) where

  opaque
    _≡ₚ_ : X → X → hProp _
    x ≡ₚ y = (x ≡ y) , transport isProp Path≡Eq (X-set _ _)

    ≡ₚ-inj : {x y : X} → (x ≡ₚ_) ≡ (y ≡ₚ_) → x ≡ y
    ≡ₚ-inj {x} {y} H = transport (idfun _) (sym $ ap fst $ happly H y) refl

  isSingleton : ℙ X → Type _
  isSingleton A = Σ[ x ∈ X ] A ≡ (x ≡ₚ_)

  Cantor-beyondSingleton : (f : ℙ X → ℙ X) → injective f → Σ[ A ∈ ℙ X ] ¬ isSingleton (f A)
  Cantor-beyondSingleton f f-inj = A , λ (x , fA≡) → noncontradiction (∈→∉ x fA≡) (∉→∈ x fA≡)
    where
    A : ℙ X
    A x = Resize $ (∀ B → f B ≡ (x ≡ₚ_) → x ∉ B) , isPropΠ3 λ _ _ _ → isProp⊥
    ∈→∉ : ∀ x → (f A ≡ (x ≡ₚ_)) → x ∈ A → x ∉ A
    ∈→∉ x fA≡ x∈A = unresize x∈A A fA≡
    ∉→∈ : ∀ x → (f A ≡ (x ≡ₚ_)) → x ∉ A → x ∈ A
    ∉→∈ x fA≡ x∉A = resize λ B fB≡ → transport (x ∉_) (f-inj (fA≡ ∙ sym fB≡)) x∉A

  module _ (P : Type ℓ′) where

    Y = Σ[ A ∈ ℙ X ] (isSingleton A ∨ Dec P)

    isSetY : isSet Y
    isSetY = isSetΣ isSetℙ λ _ → isProp→isSet squash₁

    X≤Y : X ≤ Y
    X≤Y = (λ x → (x ≡ₚ_) , inl (x , refl)) , ≡ₚ-inj ∘ (ap fst)

    dec→ℙX≤Y : Dec P → ℙ X ≤ Y
    dec→ℙX≤Y P-dec = (λ A → A , inr P-dec) , ap fst

    Y≰X : Y ≰ X
    Y≰X Y≤X@(f , f-inj) = DecNonEmpty P λ P-dec → Cantor-≰ X (≤-trans (dec→ℙX≤Y P-dec) Y≤X)

    Y≤ℙX : Y ≤ ℙ X
    Y≤ℙX = fst , λ fst-eq → Σ≡Prop (λ _ → squash₁Eq) fst-eq

    isCHType→ℙX≤Y : isCHType X Y → ∥ ℙ X ≤ Y ∥₁
    isCHType→ℙX≤Y ch-type = ch-type (X≤Y , Y≰X) Y≤ℙX

    ℙX≤Y→dec : isProp P → ℙ X ≤ Y → Dec P
    ℙX≤Y→dec P-prop ℙX≤Y with ℙX≤Y
    ... | (f , f-inj) with Cantor-beyondSingleton (fst ∘ f) (f-inj ∘ (Σ≡Prop λ _ → squash₁Eq))
    ... | (A , ¬sing) with f A
    ... | (fA , sing∨dec) = ∥∥-rec (isPropDec P-prop)
      (λ { (_⊎_.inl sing) → ⊥-rec $ ¬sing sing
          ; (_⊎_.inr dec) → dec })
      sing∨dec

    isCHType→lem : isCHType X Y → isProp P → Dec P
    isCHType→lem ch-type P-prop = ∥∥-rec (isPropDec P-prop) (ℙX≤Y→dec P-prop) (isCHType→ℙX≤Y ch-type)
```

```agda
CH→LEM : (∀ ℓ → CH ℓ) → (∀ ℓ → LEM ℓ)
CH→LEM ch ℓ P = isCHType→lem _ $ ch _ _ $ isSetY _
  where open Lemmas ℕ isSetℕ
```
