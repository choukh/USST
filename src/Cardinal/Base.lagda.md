---
title: 泛等结构集合论 (7) 直觉主义阿列夫层级
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
---

# 泛等结构集合论 (7) 直觉主义阿列夫层级

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
≤-trans : (κ : Card 𝓊) (μ : Card 𝓋) (ν : Card 𝓌) → κ ≤ μ → μ ≤ ν → κ ≤ ν
≤-trans = ∥∥₂-elim (λ _ → isSetΠ2 λ _ _ → isSet→ $ isSet→ $ ≤-set _ _)
  λ _ → ∥∥₂-elim2 (λ _ _ → isSet→ $ isSet→ $ ≤-set _ _) λ _ _ → ∥∥₁-map2 ↪-trans
```

```agda
∣⟨_⟩∣ : Ord 𝓊 → Card 𝓊
∣⟨ α ⟩∣ = ∣ ⟨ α ⟩ , ordSet ∣
```

```agda
<ₒ→≤ : α <ₒ β → ∣⟨ α ⟩∣ ≤ ∣⟨ β ⟩∣
<ₒ→≤ {β} (a , β↓a≡α) = subst (λ - → ∣⟨ - ⟩∣ ≤ ∣⟨ β ⟩∣) β↓a≡α ∣ ↑ , ↑-inj ∣₁
```

## 哈特格斯数

```agda
module Hartogs {A : Type 𝓊} (Aset : isSet A) where

  Carrier : Type (𝓊 ⁺)
  Carrier = Σ α ∶ Ord 𝓊 , ⟨ α ⟩ ≲ A

  hartogs : EmbedOrd (𝓊 ⁺) (𝓊 ⁺)
  EmbedOrd.carrier       hartogs = Carrier
  EmbedOrd._≺_           hartogs (α , _) (β , _) = α <ₒ β
  EmbedOrd.relation-prop hartogs _ _ = <ₒ-prop _ _
  EmbedOrd.target        hartogs = Ω
  EmbedOrd.embed         hartogs = fst
  EmbedOrd.inj           hartogs = Σ≡Prop λ α → squash₁
  EmbedOrd.pres≺         hartogs _ _ = idfun _
  EmbedOrd.formsInitSeg  hartogs β (α′ , le) β<ₒα′ = (β , ∥∥₁-map H le) , β<ₒα′ , refl
    where
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
  ¬ℌ↪ : ⦃ _ : PR ⦄ → ¬ ⟨ ℌ ⟩ ↪ A
  ¬ℌ↪ F@(f , f-inj) = ¬α≃ₒα↓a ℌ h $
    ℌ       ≃ₒ˘⟨ ℌ⁻≃ₒℌ ⟩
    ℌ⁻      ≃ₒ⟨ α≃Ω↓α ⟩
    Ω ↓ ℌ⁻  ≃ₒ⟨ isoToEquiv j , mkIsOrderEquiv ordEquiv ⟩
    ℌ ↓ h   ≃ₒ∎
    where
    B : Type 𝓊
    B = Σ y ∶ A , ⟨ Resize {𝓋 = 𝓊} $ P y ⟩
      where
      P : A → hProp (𝓊 ⁺)
      P y = fiber f y , hasPropFb y
        where
        hasPropFb : hasPropFibers f
        hasPropFb _ (a , p) (b , q) = Σ≡Prop (λ _ → Aset _ _) (f-inj $ p ∙ sym q)
    i : Iso B ⟨ ℌ ⟩
    Iso.fun i (y , H) = unresize H .fst
    Iso.inv i x = f x , resize (x , refl)
    Iso.leftInv i (y , H) = Σ≡Prop (λ _ → isPropResize) (unresize H .snd)
    Iso.rightInv i a = Σ≡Prop (λ _ → squash₁) $ cong fst H where
      H : fst (unresize (resize _)) ≡ a
      H = subst (λ - → fst - ≡ _) (sym $ retIsEq isEquivResize _) refl
    ℌ⁻ : Ord 𝓊
    ℌ⁻ = ResizeOrd B ℌ $ isoToEquiv i
    ℌ⁻≃ₒℌ : ℌ⁻ ≃ₒ ℌ
    ℌ⁻≃ₒℌ = ResizeOrdEquiv B ℌ (isoToEquiv i)
    ℌ⁻≲A : ⟨ ℌ⁻ ⟩ ≲ A
    ℌ⁻≲A = ≈-≲-trans ∣ ℌ⁻≃ₒℌ .fst ∣₁ ∣ F ∣₁
    h : ⟨ ℌ ⟩
    h = ℌ⁻ , ℌ⁻≲A
    j : Iso ⟨ Ω ↓ ℌ⁻ ⟩ ⟨ ℌ ↓ h ⟩
    j = {!   !}
    ordEquiv : ∀ x y → x ≺⟨ Ω ↓ ℌ⁻ ⟩ y ≃ (Iso.fun j) x ≺⟨ ℌ ↓ h ⟩ (Iso.fun j) y
    ordEquiv _ _ = {!   !} --idEquiv _
```

```agda
  <ℌ→≲A : ∀ α → α <ₒ ℌ → ⟨ α ⟩ ≲ A
  <ℌ→≲A α ((β , β≤) , eq) = ∥∥₁-map (↪-trans H) β≤
    where
    f : ⟨ ℌ ↓ (β , β≤) ⟩ → ⟨ β ⟩
    f (_ , b , _) = b
    f-inj : injective f
    f-inj {(γ , γ≤) , a , β↓a≡γ} {(δ , δ≤) , b , β↓b≡δ} a≡b =
      Σ≡Prop (λ _ → <ₒ-prop _ _) (Σ≡Prop (λ _ → squash₁) γ≡δ) where
      γ≡δ = sym β↓a≡γ ∙ cong (β ↓_) a≡b ∙ β↓b≡δ
    H : ⟨ α ⟩ ↪ ⟨ β ⟩
    H = subst (λ α → ⟨ α ⟩ ↪ ⟨ β ⟩) eq (f , f-inj)
```
