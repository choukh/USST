---
title: 泛等结构集合论 (7) 哈特格斯数
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
---

# 泛等结构集合论 (7) 哈特格斯数

> 交流Q群: 893531731  
> 本文源码: [Cardinal.Hartogs.lagda.md](https://github.com/choukh/USST/blob/main/src/Cardinal/Hartogs.lagda.md)  
> 高亮渲染: [Cardinal.Hartogs.html](https://choukh.github.io/USST/Cardinal.Hartogs.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --hidden-argument-puns #-}

module Cardinal.Hartogs where
open import Preliminary
open import Ordinal renaming ( _≤_ to _≤ₒ_; ≤-prop to ≤ₒ-prop
                             ; _<_ to _<ₒ_; <-prop to <ₒ-prop)
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
```

## 哈特格斯数

```agda
module Pre {A : Type 𝓊} (A-set : isSet A) where

  hartogs : EmbedOrd (𝓊 ⁺) (𝓊 ⁺)
  EmbedOrd.carrier       hartogs = Σ (B , strB) ∶ Ord 𝓊 , ∣ B , OrdStr.underlying-set strB ∣₂ ≤ ∣ A , A-set ∣₂
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

  ℍ→ℙ³-inj : injective ℍ→ℙ³
  ℍ→ℙ³-inj = {!   !}
```

```agda
  resizeCarrier : ⦃ _ : PR ⦄ → Type (𝓊 ⁺)
  resizeCarrier = Σ X ∶ ℙ⁺ 2 A 𝓊 , Σ a ∶ ⟨ ℍ ⟩ , {!   !} ≡ X
```

回想我们有: 假设 `PR`, 可以将任意 `β : Ord 𝓋` 调整到 `Ord 𝓊` 上, 只要找到一个 `A : Type 𝓊` 满足 `A ≃ ⟨ β ⟩`.

```agda
  _ : ⦃ _ : PR ⦄ (A : Type 𝓊) (β : Ord 𝓋) → A ≃ ⟨ β ⟩ → Ord 𝓊
  _ = ResizeOrd
```
