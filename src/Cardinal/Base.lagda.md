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
open import Preliminary
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
_≤ₕ_ : Card 𝓊 → Card 𝓋 → hProp (𝓊 ⊔ 𝓋)
_≤ₕ_ = ∥∥₂-rec2 isSetHProp λ (A , _) (B , _) → ∥ A ↪ B ∥₁ , squash₁
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
∣⟨ α ⟩∣ = ∣ ⟨ α ⟩ , ordSet ∣₂
```

```agda
<ₒ→≤ : α <ₒ β → ∣⟨ α ⟩∣ ≤ ∣⟨ β ⟩∣
<ₒ→≤ {β} (a , β↓a≡α) = subst (λ - → ∣⟨ - ⟩∣ ≤ ∣⟨ β ⟩∣) β↓a≡α ∣ ↑ , ↑-inj ∣₁
```

## 直谓哈特格斯数

```agda
module PredicativeHartogs {A : Type 𝓊} (Aset : isSet A) where

  hartogs : EmbedOrd (𝓊 ⁺) (𝓊 ⁺)
  EmbedOrd.carrier       hartogs = Σ α ∶ Ord 𝓊 , ∣⟨ α ⟩∣ ≤ ∣ A , Aset ∣₂
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
  ℍ : Ord (𝓊 ⁺)
  ℍ = tieup hartogs
```

```agda
  ℍ→ℙ³ : ⟨ ℍ ⟩ → ℙ (ℙ (ℙ A))
  ℍ→ℙ³ (β , _) X = Lift ∥ Iso Sub ⟨ β ⟩ ∥₁ , isOfHLevelLift 1 squash₁
    where Sub = Σ (x , _) ∶ ⟦ X ⟧ , Σ (y , _) ∶ ⟦ X ⟧ , x ⊂ y
```

```agda
  ℍ→ℙ³-inj : injective ℍ→ℙ³
  ℍ→ℙ³-inj = {!   !}
```

```agda
  ℍ↪ℙ³ : ⟨ ℍ ⟩ ↪ ℙ (ℙ (ℙ A))
  ℍ↪ℙ³ = ℍ→ℙ³ , ℍ→ℙ³-inj
```

## 非直谓哈特格斯数

现在假设 `PR`.

```agda
module ImpredicativeHartogs ⦃ _ : PR ⦄ {A : Type (𝓊 ⁺)} (Aset : isSet A) where
  open PredicativeHartogs Aset renaming (ℍ to ℍₚ; ℍ↪ℙ³ to ℍₚ↪ℙ³)
```

```agda
  ℍ-injected : ℙ[ 𝓊 ][ 2 ]⁺ A → hProp 𝓊
  ℍ-injected y = Resize $ (∃ x ∶ ⟨ ℍₚ ⟩ , Resizeℙ³ (ℍ→ℙ³ x) ≡ y) , squash₁

  isPropℍInjected : {x : ℙ[ 𝓊 ][ 2 ]⁺ A} → isProp ⟨ ℍ-injected x ⟩
  isPropℍInjected = ℍ-injected _ .snd
```

```agda
  carrier : Type (𝓊 ⁺)
  carrier = Σ (ℙ[ 𝓊 ][ 2 ]⁺ A) (⟨_⟩ ∘ ℍ-injected)
```

```agda
  isSetCarrier : isSet carrier
  isSetCarrier = isSetΣ (isSetΠ λ _ → isSetHProp) λ x → isProp→isSet isPropℍInjected
```

```agda
  carrierMap : ⟨ ℍₚ ⟩ → carrier
  carrierMap x = Resizeℙ³ (ℍ→ℙ³ x) , resize ∣ x , refl ∣₁

  carrierEquiv : carrier ≃ ⟨ ℍₚ ⟩
  carrierEquiv = invEquiv $ carrierMap , inj→sur→isEquiv isSetCarrier inj sur
    where
    inj : injective carrierMap
    inj = ℍ→ℙ³-inj ∘ Resizeℙ³-inj ∘ cong fst
    sur : surjective carrierMap
    sur (y , H) = ∥∥₁-map (λ (x , fx≡y) → x , Σ≡Prop (λ _ → isPropℍInjected) fx≡y) (unresize H)
```

回想我们有序数降级: 任意 `β : Ord 𝓋` 可以降级到 `Ord 𝓊` 上, 只要找到一个 `A : Type 𝓊` 满足 `A ≃ ⟨ β ⟩`.

```agda
  _ : (A : Type 𝓊) (β : Ord 𝓋) → A ≃ ⟨ β ⟩ → Ord 𝓊
  _ = ResizeOrd
```

```agda
  ℍ : Ord (𝓊 ⁺)
  ℍ = ResizeOrd carrier ℍₚ carrierEquiv

  ℍ≃ℍₚ : ℍ ≃ₒ ℍₚ
  ℍ≃ℍₚ = ResizeOrdEquiv _ _ carrierEquiv
```

```agda
  ℍ↪ℙ³ : ⟨ ℍ ⟩ ↪ ℙ[ 𝓊 ][ 2 ]⁺ A
  ℍ↪ℙ³ = fst , Σ≡Prop (λ _ → isPropℍInjected)
```

```agda
  ¬ℍ↪ : ¬ ⟨ ℍ ⟩ ↪ A
  ¬ℍ↪ Inj@(f , f-inj) = ¬α≃ₒα↓a ℍₚ (ℍ , ∣ℍ∣≤∣A∣) $
    ℍₚ                  ≃ₒ˘⟨ ℍ≃ℍₚ ⟩
    ℍ                   ≃ₒ⟨ α≃Ω↓α ⟩
    Ω ↓ ℍ               ≃ₒ⟨ isoToEquiv i , mkIsOrderEquiv ordEquiv ⟩
    ℍₚ ↓ (ℍ , ∣ℍ∣≤∣A∣)  ≃ₒ∎
    where
    ∣ℍ∣≤∣A∣ : ∣⟨ ℍ ⟩∣ ≤ ∣ A , Aset ∣₂
    ∣ℍ∣≤∣A∣ = ∣ Inj ∣₁
    i : Iso ⟨ Ω ↓ ℍ ⟩ ⟨ ℍₚ ↓ (ℍ , ∣ℍ∣≤∣A∣) ⟩
    Iso.fun i (α , α≺ℍ) = (α , H₁) , H₂ where
      H₁ : ∣⟨ α ⟩∣ ≤ ∣ A , Aset ∣₂
      H₁ = ≤-trans ∣⟨ α ⟩∣ ∣⟨ ℍ ⟩∣ ∣ A , Aset ∣₂ (<ₒ→≤ α≺ℍ) ∣ℍ∣≤∣A∣
      H₂ : (α , H₁) ≺⟨ ℍₚ ⟩ (ℍ , ∣ℍ∣≤∣A∣)
      H₂ = unresize {𝓋 = 𝓊 ⁺ ⁺} (resize {P = _ , <ₒ-prop _ _} α≺ℍ)
    Iso.inv i ((α , _) , α≺ℍ) = α , unresize {𝓋 = 𝓊 ⁺ ⁺} (resize {P = _ , <ₒ-prop _ _} α≺ℍ)
    Iso.rightInv i _ = Σ≡Prop (λ _ → <ₒ-prop _ _) (Σ≡Prop (λ _ → ≤-prop _ _) refl)
    Iso.leftInv i _ = Σ≡Prop (λ _ → <ₒ-prop _ _) refl
    ordEquiv : ∀ x y → x ≺⟨ Ω ↓ ℍ ⟩ y ≃ (Iso.fun i) x ≺⟨ ℍₚ ↓ (ℍ , ∣ℍ∣≤∣A∣) ⟩ (Iso.fun i) y
    ordEquiv _ _ = idEquiv _
```
