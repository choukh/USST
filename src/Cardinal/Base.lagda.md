---
title: 泛等结构集合论 (7) 基数
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
---

# 泛等结构集合论 (7) 基数

> 交流Q群: 893531731  
> 本文源码: [Cardinal.Base.lagda.md](https://github.com/choukh/USST/blob/main/src/Cardinal/Base.lagda.md)  
> 高亮渲染: [Cardinal.Base.html](https://choukh.github.io/USST/Cardinal.Base.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification --hidden-argument-puns #-}

module Cardinal.Base where
open import Preliminary renaming (∣_∣₂ to ∣_∣)
open import Ordinal hiding (≤-refl; ≤-trans)
  renaming ( _≤_ to _≤ₒ_; ≤-prop to ≤ₒ-prop
           ; _<_ to _<ₒ_; <-prop to <ₒ-prop)
open BinaryRelation
```

## 基数

```agda
Card : (𝓊 : Level) → Type (𝓊 ⁺)
Card 𝓊 = ∥ hSet 𝓊 ∥₂
```

```agda
isSetCard : isSet (Card 𝓊)
isSetCard = squash₂
```

```agda
cardRec : (hSet 𝓊 → hProp (𝓊 ⁺)) → Card 𝓊 → hProp (𝓊 ⁺)
cardRec P = ∥∥₂-rec {B = hProp _} isSetHProp P
```

```agda
cardEqIso∥Eq∥ : {a b : hSet 𝓊} → Iso (∣ a ∣ ≡ ∣ b ∣) ∥ a ≡ b ∥₁
Iso.fun (cardEqIso∥Eq∥ {𝓊} {b}) p = subst (λ κ → cardRec (λ a → ∥ a ≡ b ∥ₚ) κ .fst) (sym p) ∣ refl ∣₁
Iso.inv       cardEqIso∥Eq∥ = ∥∥₁-rec (isSetCard _ _) (cong ∣_∣)
Iso.rightInv  cardEqIso∥Eq∥ _ = squash₁ _ _
Iso.leftInv   cardEqIso∥Eq∥ _ = isSetCard _ _ _ _
```

```agda
equivToCardEq : {a b : hSet 𝓊} → ⟨ a ⟩ ≃ ⟨ b ⟩ → ∣ a ∣ ≡ ∣ b ∣
equivToCardEq eqv = cong ∣_∣ $ Σ≡Prop (λ _ → isPropΠ2 λ _ _ → isPropIsProp) (ua eqv)
```

```agda
cardEqToEquip : {a b : hSet 𝓊} → ∣ a ∣ ≡ ∣ b ∣ → ⟨ a ⟩ ≈ ⟨ b ⟩
cardEqToEquip eq = ∥∥₁-map (λ x → subst (λ - → _ ≃ ⟨ - ⟩) x (idEquiv _)) (Iso.fun cardEqIso∥Eq∥ eq)
```

```agda
cardEqIsoEquip : {a b : hSet 𝓊} → Iso (∣ a ∣ ≡ ∣ b ∣) (⟨ a ⟩ ≈ ⟨ b ⟩)
Iso.fun       cardEqIsoEquip = cardEqToEquip
Iso.inv       cardEqIsoEquip = ∥∥₁-rec (isSetCard _ _) equivToCardEq
Iso.rightInv  cardEqIsoEquip _ = squash₁ _ _
Iso.leftInv   cardEqIsoEquip _ = isSetCard _ _ _ _
```

```agda
cardEq≃Equip : {a b : hSet 𝓊} → (∣ a ∣ ≡ ∣ b ∣) ≃ (⟨ a ⟩ ≈ ⟨ b ⟩)
cardEq≃Equip = isoToEquiv cardEqIsoEquip
```

## 基数的序

```agda
_≤ₕ_ : Card 𝓊 → Card 𝓋 → hProp (𝓊 ⊔ 𝓋)
_≤ₕ_ = ∥∥₂-rec2 isSetHProp λ (A , _) (B , _) → A ≲ B , squash₁
```

```agda
_≤_ : Card 𝓊 → Card 𝓋 → Type (𝓊 ⊔ 𝓋)
κ ≤ μ = ⟨ κ ≤ₕ μ ⟩

≤-prop : (κ : Card 𝓊) (μ : Card 𝓋) → isProp (κ ≤ μ)
≤-prop κ μ = str (κ ≤ₕ μ)

≤-set : (κ : Card 𝓊) (μ : Card 𝓋) → isSet (κ ≤ μ)
≤-set κ μ = isProp→isSet (≤-prop κ μ)
```

```agda
≤-refl : (κ : Card 𝓊) → κ ≤ κ
≤-refl = ∥∥₂-elim (λ _ → ≤-set _ _) λ _ → ∣ ↪-refl ∣₁
```

```agda
≤-trans : (κ μ ν : Card 𝓊) → κ ≤ μ → μ ≤ ν → κ ≤ ν
≤-trans = ∥∥₂-elim3 (λ _ _ _ → isSetΠ2 λ _ _ → ≤-set _ _) λ _ _ _ → ∥∥₁-map2 ↪-trans
```

```agda
∣⟨_⟩∣ : Ord 𝓊 → Card 𝓊
∣⟨ α ⟩∣ = ∣ ⟨ α ⟩ , ordSet ∣
```

```agda
<ₒ→≤ : α <ₒ β → ∣⟨ α ⟩∣ ≤ ∣⟨ β ⟩∣
<ₒ→≤ {β} (a , β↓a≡α) = subst (λ - → ∣⟨ - ⟩∣ ≤ ∣⟨ β ⟩∣) β↓a≡α ∣ ↑ , ↑-inj ∣₁
```

## 直谓哈特格斯数

```agda
module PredicativeHartogs {A : Type 𝓊} (Aset : isSet A) where

  hartogs : EmbedOrd (𝓊 ⁺) (𝓊 ⁺)
  EmbedOrd.carrier       hartogs = Σ α ∶ Ord 𝓊 , ∣⟨ α ⟩∣ ≤ ∣ A , Aset ∣
  EmbedOrd._≺_           hartogs (α , _) (β , _) = α <ₒ β
  EmbedOrd.relation-prop hartogs _ _ = <ₒ-prop _ _
  EmbedOrd.target        hartogs = Ω
  EmbedOrd.embed         hartogs = fst
  EmbedOrd.inj           hartogs = Σ≡Prop λ _ → ≤-prop _ _
  EmbedOrd.pres≺         hartogs _ _ = idfun _
  EmbedOrd.formsInitSeg  hartogs β (α′ , le) β<ₒα′ = (β , ∥∥₁-map H le) , β<ₒα′ , refl where
    H : ⟨ α′ ⟩ ↪ A → Σ (⟨ β ⟩ → A) injective
    H (f , f-inj) = f ∘ g , g-inj ∘ f-inj where
      g = <→≤ β<ₒα′ .fst
      g-inj = IsOrdEmbed.inj $ <→≤ β<ₒα′ .snd
```

```agda
  ℌ : Ord (𝓊 ⁺)
  ℌ = tieup hartogs
```

```agda
  <ℌ→≲A : ∀ α → α <ₒ ℌ → ⟨ α ⟩ ≲ A
  <ℌ→≲A α ((β , β≤) , eq) = ∥∥₁-map (↪-trans H) β≤
    where
    f : ⟨ ℌ ↓ (β , β≤) ⟩ → ⟨ β ⟩
    f (_ , b , _) = b
    f-inj : injective f
    f-inj {(γ , γ≤) , a , β↓a≡γ} {(δ , δ≤) , b , β↓b≡δ} a≡b =
      Σ≡Prop (λ _ → <ₒ-prop _ _) (Σ≡Prop (λ _ → ≤-prop _ _) γ≡δ) where
      γ≡δ = sym β↓a≡γ ∙ cong (β ↓_) a≡b ∙ β↓b≡δ
    H : ⟨ α ⟩ ↪ ⟨ β ⟩
    H = subst (λ α → ⟨ α ⟩ ↪ ⟨ β ⟩) eq (f , f-inj)
```

```agda
  Sub : (P : ℙ (ℙ A)) → ⟦ P ⟧ → ⟦ P ⟧ → Type (𝓊 ⁺)
  Sub _ (x , _) (y , _) = Lift (x ⊂ y)

  （_,_） : (P : ℙ (ℙ A)) (wo : WellOrdered (Sub P)) → Ord (𝓊 ⁺)
  （ P , wo ） = ⟦ P ⟧ , mkOrdStr (Sub P) wo
```

```agda
  ℌ→ℙ³ : ⟨ ℌ ⟩ → ℙ (ℙ (ℙ A))
  ℌ→ℙ³ a@(α , _) P = (Σ wo ∶ WellOrdered (Sub P) , （ P , wo ） ≃ₒ LiftOrd α) ,
    isPropΣ (isPropWellOrdered _) λ _ → isPropOrdEquiv _ _
```

```agda
  ℌ→ℙ³-inj : injective ℌ→ℙ³
  ℌ→ℙ³-inj a@{α , α≤} {β , β≤} eq = Σ≡Prop (λ _ → ≤-prop _ _) (∥∥₁-rec (isSetOrd _ _) e α≤)
    where
    e : ⟨ α ⟩ ↪ A → α ≡ β
    e (f , f-inj) = ≃ₒ→≡ $
      α           ≃ₒ⟨ LiftOrdEquiv ⟩
      LiftOrd α   ≃ₒ˘⟨ eα ⟩
      （ P , wo ）  ≃ₒ⟨ eβ ⟩
      LiftOrd β   ≃ₒ˘⟨ LiftOrdEquiv ⟩
      β           ≃ₒ∎
      where
      P : ℙ (ℙ A)
      P p = ∥ Lift $ Σ a′ ∶ ⟨ α ⟩ , (∀ b → ⟨ p b ⟩ ↔ (Σ a ∶ ⟨ α ⟩ , a ≺⟨ α ⟩ a′ × f a ≡ b)) ∥ₚ
      wo : WellOrdered (Sub P)
      wo = {!   !}
      eα : （ P , wo ） ≃ₒ LiftOrd α
      eα = {!   !}
      Σwo : Σ wo ∶ WellOrdered (Sub P) , （ P , wo ） ≃ₒ LiftOrd β
      Σwo = transport (cong fst (funExt⁻ eq P)) (wo , eα)
      eβ : （ P , wo ） ≃ₒ LiftOrd β
      eβ = subst (λ wo → （ P , wo ） ≃ₒ LiftOrd β) (isPropWellOrdered _ _ _) $ Σwo .snd
```

## 非直谓哈特格斯数

现在假设 `PR`.

```agda
module ImpredicativeHartogs ⦃ _ : PR ⦄ {A : Type (𝓊 ⁺)} (Aset : isSet A) where
  open PredicativeHartogs Aset renaming (ℌ to ℌₚ; <ℌ→≲A to <ℌₚ→≲A)
```

```agda
  ℌ-injected : ℙ[ 𝓊 ][ 2 ]⁺ A → hProp 𝓊
  ℌ-injected y = Resize $ ∥ Σ x ∶ ⟨ ℌₚ ⟩ , Resizeℙ³ (ℌ→ℙ³ x) ≡ y ∥ₚ

  isPropℌInjected : {x : ℙ[ 𝓊 ][ 2 ]⁺ A} → isProp ⟨ ℌ-injected x ⟩
  isPropℌInjected = ℌ-injected _ .snd
```

```agda
  carrier : Type (𝓊 ⁺)
  carrier = Σ (ℙ[ 𝓊 ][ 2 ]⁺ A) (⟨_⟩ ∘ ℌ-injected)
```

```agda
  isSetCarrier : isSet carrier
  isSetCarrier = isSetΣ (isSetΠ λ _ → isSetHProp) λ x → isProp→isSet isPropℌInjected
```

```agda
  carrierMap : ⟨ ℌₚ ⟩ → carrier
  carrierMap x = Resizeℙ³ (ℌ→ℙ³ x) , resize ∣ x , refl ∣₁

  carrierEquiv : carrier ≃ ⟨ ℌₚ ⟩
  carrierEquiv = invEquiv $ carrierMap , inj→sur→isEquiv isSetCarrier inj sur
    where
    inj : injective carrierMap
    inj = ℌ→ℙ³-inj ∘ Resizeℙ³-inj ∘ cong fst
    sur : surjective carrierMap
    sur (y , H) = ∥∥₁-map (λ (x , fx≡y) → x , Σ≡Prop (λ _ → isPropℌInjected) fx≡y) (unresize H)
```

回想我们有序数降级: 任意 `β : Ord 𝓋` 可以降级到 `Ord 𝓊` 上, 只要找到一个 `A : Type 𝓊` 满足 `A ≃ ⟨ β ⟩`.

```agda
  _ : (A : Type 𝓊) (β : Ord 𝓋) → A ≃ ⟨ β ⟩ → Ord 𝓊
  _ = ResizeOrd
```

```agda
  ℌ : Ord (𝓊 ⁺)
  ℌ = ResizeOrd carrier ℌₚ carrierEquiv

  ℌ≃ₒℌₚ : ℌ ≃ₒ ℌₚ
  ℌ≃ₒℌₚ = ResizeOrdEquiv _ _ carrierEquiv
```

```agda
  ℌ↪ℙ³ : ⟨ ℌ ⟩ ↪ ℙ[ 𝓊 ][ 2 ]⁺ A
  ℌ↪ℙ³ = fst , Σ≡Prop (λ _ → isPropℌInjected)
```

```agda
  ¬ℌ↪ : ¬ ⟨ ℌ ⟩ ↪ A
  ¬ℌ↪ Inj@(f , f-inj) = ¬α≃ₒα↓a ℌₚ (ℌ , ∣ℌ∣≤∣A∣) $
    ℌₚ                  ≃ₒ˘⟨ ℌ≃ₒℌₚ ⟩
    ℌ                   ≃ₒ⟨ α≃Ω↓α ⟩
    Ω ↓ ℌ               ≃ₒ⟨ isoToEquiv i , mkIsOrderEquiv ordEquiv ⟩
    ℌₚ ↓ (ℌ , ∣ℌ∣≤∣A∣)  ≃ₒ∎
    where
    ∣ℌ∣≤∣A∣ : ∣⟨ ℌ ⟩∣ ≤ ∣ A , Aset ∣
    ∣ℌ∣≤∣A∣ = ∣ Inj ∣₁
    i : Iso ⟨ Ω ↓ ℌ ⟩ ⟨ ℌₚ ↓ (ℌ , ∣ℌ∣≤∣A∣) ⟩
    Iso.fun i (α , α≺ℌ) = (α , H₁) , H₂ where
      H₁ : ∣⟨ α ⟩∣ ≤ ∣ A , Aset ∣
      H₁ = ≤-trans ∣⟨ α ⟩∣ ∣⟨ ℌ ⟩∣ ∣ A , Aset ∣ (<ₒ→≤ α≺ℌ) ∣ℌ∣≤∣A∣
      H₂ : (α , H₁) ≺⟨ ℌₚ ⟩ (ℌ , ∣ℌ∣≤∣A∣)
      H₂ = unresize {𝓋 = 𝓊 ⁺ ⁺} (resize {P = _ , <ₒ-prop _ _} α≺ℌ)
    Iso.inv i ((α , _) , α≺ℌ) = α , unresize {𝓋 = 𝓊 ⁺ ⁺} (resize {P = _ , <ₒ-prop _ _} α≺ℌ)
    Iso.rightInv i _ = Σ≡Prop (λ _ → <ₒ-prop _ _) (Σ≡Prop (λ _ → ≤-prop _ _) refl)
    Iso.leftInv i _ = Σ≡Prop (λ _ → <ₒ-prop _ _) refl
    ordEquiv : ∀ x y → x ≺⟨ Ω ↓ ℌ ⟩ y ≃ (Iso.fun i) x ≺⟨ ℌₚ ↓ (ℌ , ∣ℌ∣≤∣A∣) ⟩ (Iso.fun i) y
    ordEquiv _ _ = idEquiv _
```

```agda
  <ℌ→≲A : ∀ α → α <ₒ ℌ → ⟨ α ⟩ ≲ A
  <ℌ→≲A α α<ₒℌ = ≈-≲-trans ∣ LiftOrdEquiv .fst ∣₁ $ <ℌₚ→≲A (LiftOrd α) H where
    H : LiftOrd α <ₒ ℌₚ
    H = <-cong≃ₒ LiftOrdEquiv ℌ≃ₒℌₚ α<ₒℌ
```
