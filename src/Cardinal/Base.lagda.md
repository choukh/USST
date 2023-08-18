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
module Hartogs ⦃ _ : PR ⦄ {A : Type 𝓊} (Aset : isSet A) where

  Carrier : (𝓋 : Level) → Type (𝓋 ⁺)
  Carrier 𝓋 = Σ α ∶ Ord 𝓋 , ⟨ Resize {𝓋 = 𝓋} (∣⟨ α ⟩∣ ≤ₕ ∣ A , Aset ∣) ⟩
  -- ∣ (Σ (Card 𝓊) λ κ → κ ≤ μ) , sethood ∣₂
  -- ∣ (Σ (Card 𝓋) λ κ → κ ≤ μ) , sethood ∣₂

  hartogs : EmbedOrd (𝓋 ⁺) (𝓋 ⁺)
  EmbedOrd.carrier       (hartogs {𝓋}) = Carrier 𝓋
  EmbedOrd._≺_           hartogs (α , _) (β , _) = α <ₒ β
  EmbedOrd.relation-prop hartogs _ _ = <ₒ-prop _ _
  EmbedOrd.target        hartogs = Ω
  EmbedOrd.embed         hartogs = fst
  EmbedOrd.inj           hartogs = Σ≡Prop λ α → isPropResize
  EmbedOrd.pres≺         hartogs _ _ = idfun _
  EmbedOrd.formsInitSeg  hartogs β (α′ , le) β<ₒα′ = (β , resize∥∥-map H le) , β<ₒα′ , refl
    where
    H : ⟨ α′ ⟩ ↪ A → Σ (⟨ β ⟩ → A) injective
    H (f , f-inj) = f ∘ g , g-inj ∘ f-inj where
      g = <→≤ β<ₒα′ .fst
      g-inj = IsOrdEmbed.inj $ <→≤ β<ₒα′ .snd
```

```agda
  module _ (𝓋 : Level) where
    ℌ⁻ : Ord (𝓋 ⁺)
    ℌ⁻ = tieup hartogs

    ℌ : Ord (𝓋 ⁺ ⁺)
    ℌ = tieup hartogs

    ℌ⁺ : Ord (𝓋 ⁺ ⁺ ⁺)
    ℌ⁺ = tieup hartogs
```

```agda
    ℌ≃ₒℌ⁺ : ℌ ≃ₒ ℌ⁺
    ℌ≃ₒℌ⁺ = e , mkIsOrderEquiv ordEquiv
      where
      f : ⟨ ℌ ⟩ → ⟨ ℌ⁺ ⟩
      f (α , α≤) = (LiftOrd α) , resize∥∥-map g α≤
        where
        g : ⟨ α ⟩ ↪ A → ⟨ LiftOrd α ⟩ ↪ A
        g (h , h-inj) = h ∘ lower , liftExt ∘ h-inj
      f-equiv : isEquiv f
      f-equiv = inj→sur→isEquiv ordSet inj sur
        where
        inj : injective f
        inj {α , _} {β , _} eq = Σ≡Prop (λ _ → isPropResize) $ ≃ₒ→≡ $
          α         ≃ₒ⟨ LiftOrdEquiv ⟩
          LiftOrd α ≃ₒ⟨ ≡→≃ₒ $ cong fst eq ⟩
          LiftOrd β ≃ₒ˘⟨ LiftOrdEquiv ⟩
          β         ≃ₒ∎
        sur : surjective f
        sur (γ , γ≤) = ∣ (ξ , {!   !}) , {!   !} ∣₁
          where
          ξ : Ord (𝓋 ⁺)
          ξ = ResizeOrd {!   !} γ {!   !}
      g : ⟨ ℌ⁺ ⟩ → ⟨ ℌ ⟩
      g (α , α≤) = {!   !} , {!   !}
      e : ⟨ ℌ ⟩ ≃ ⟨ ℌ⁺ ⟩
      e = f , f-equiv
      ordEquiv : ∀ x y → x ≺⟨ ℌ ⟩ y ≃ (e ⁺¹) x ≺⟨ ℌ⁺ ⟩ (e ⁺¹) y
      ordEquiv _ _ = {!   !}
```

```agda
    ¬ℌ↪ : ¬ ⟨ ℌ ⟩ ↪ A
    ¬ℌ↪ Inj@(f , f-inj) = ¬α≃ₒα↓a ℌ⁺ h $
      ℌ⁺     ≃ₒ˘⟨ ℌ≃ₒℌ⁺ ⟩
      ℌ      ≃ₒ⟨ α≃Ω↓α ⟩
      Ω ↓ ℌ  ≃ₒ⟨ isoToEquiv i , mkIsOrderEquiv ordEquiv ⟩
      ℌ⁺ ↓ h ≃ₒ∎
      -- ℌ = ℌ⁺ ↓ h < ℌ⁺ ≤ ℌ
      where
      ∣ℌ∣≤∣A∣ : ∣⟨ ℌ ⟩∣ ≤ ∣ A , Aset ∣
      ∣ℌ∣≤∣A∣ = ∣ Inj ∣₁
      h : ⟨ ℌ⁺ ⟩
      h = ℌ , resize ∣ℌ∣≤∣A∣
      i : Iso ⟨ Ω ↓ ℌ ⟩ ⟨ ℌ⁺ ↓ h ⟩
      Iso.fun i (α , α≺ℌ) = (α , resize H₁) , H₂
        where
        H₁ : ∣⟨ α ⟩∣ ≤ ∣ A , Aset ∣
        H₁ = ≤-trans ∣⟨ α ⟩∣ ∣⟨ ℌ ⟩∣ ∣ A , Aset ∣ (<ₒ→≤ α≺ℌ) ∣ℌ∣≤∣A∣
        H₂ : (α , resize H₁) ≺⟨ ℌ⁺ ⟩ h
        H₂ = unresize {𝓋 = 𝓋 ⁺} (resize {P = _ , <ₒ-prop _ _} α≺ℌ)
      Iso.inv i ((α , _) , α≺ℌ) = α , unresize {𝓋 = 𝓋 ⁺} (resize {P = _ , <ₒ-prop _ _} α≺ℌ)
      Iso.rightInv i _ = Σ≡Prop (λ _ → <ₒ-prop _ _) (Σ≡Prop (λ _ → isPropResize) refl)
      Iso.leftInv i _ = Σ≡Prop (λ _ → <ₒ-prop _ _) refl
      ordEquiv : ∀ x y → x ≺⟨ Ω ↓ ℌ ⟩ y ≃ (Iso.fun i) x ≺⟨ ℌ⁺ ↓ h ⟩ (Iso.fun i) y
      ordEquiv _ _ = idEquiv _
```

```agda
    <ℌ→≲A : ∀ α → α <ₒ ℌ → ⟨ α ⟩ ≲ A
    <ℌ→≲A α ((β , β≤) , eq) = ∥∥₁-map (↪-trans H) (unresize β≤)
      where
      f : ⟨ ℌ ↓ (β , β≤) ⟩ → ⟨ β ⟩
      f (_ , b , _) = b
      f-inj : injective f
      f-inj {(γ , γ≤) , a , β↓a≡γ} {(δ , δ≤) , b , β↓b≡δ} a≡b =
        Σ≡Prop (λ _ → <ₒ-prop _ _) (Σ≡Prop (λ _ → isPropResize) γ≡δ) where
        γ≡δ = sym β↓a≡γ ∙ cong (β ↓_) a≡b ∙ β↓b≡δ
      H : ⟨ α ⟩ ↪ ⟨ β ⟩
      H = subst (λ α → ⟨ α ⟩ ↪ ⟨ β ⟩) eq (f , f-inj)
```
