---
title: 泛等结构集合论 (6) 哈特格斯数
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
---

# 泛等结构集合论 (6) 哈特格斯数

> 交流Q群: 893531731  
> 本文源码: [Cardinal.Hartogs.lagda.md](https://github.com/choukh/USST/blob/main/src/Cardinal/Hartogs.lagda.md)  
> 高亮渲染: [Cardinal.Hartogs.html](https://choukh.github.io/USST/Cardinal.Hartogs.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module Cardinal.Hartogs where
open import Preliminary
open import Ordinal renaming ( _≤_ to _≤ₒ_; ≤-prop to ≤ₒ-prop
                             ; _<_ to _<ₒ_; <-prop to <ₒ-prop)
```

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

```agda
module Pre {A : Type 𝓊} (A-set : isSet A) where

  hartogs : EmbeddedOrd (𝓊 ⁺)
  EmbeddedOrd.carrier       hartogs = Σ (B , strB) ∶ Ord 𝓊 , ∣ B , OrdStr.underlying-set strB ∣₂ ≤ ∣ A , A-set ∣₂
  EmbeddedOrd._≺_           hartogs (α , _) (β , _) = α <ₒ β
  EmbeddedOrd.relation-prop hartogs _ _ = <ₒ-prop _ _
  EmbeddedOrd.target        hartogs = Ω
  EmbeddedOrd.embed         hartogs = fst
  EmbeddedOrd.inj           hartogs = Σ≡Prop λ _ → ≤-prop _ _
  EmbeddedOrd.pres≺         hartogs _ _ = idfun _
  EmbeddedOrd.formsInitSeg  hartogs β (α′ , le) β<ₒα′ = (β , ∥∥₁-map H le) , β<ₒα′ , refl where
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
--resize
```


  ℍ→ℙ³ : ⟨ ℍ ⟩ → ℙ (ℙ (ℙ A))
  ℍ→ℙ³ (β , le) X = ((Σ (ℙ $ ℙ A) λ X → Lt ⟪ X ⟫) ≃ ⟨ β ⟩) , {!   !}
    where
    ⟪_⟫ : ∀ {𝓊} {X : Type 𝓊} → ℙ X → Type _
    ⟪ A ⟫ = Σ _ (_∈ A)
  
    record Lt (X : Type (𝓊 ⁺)) : Type (𝓊 ⁺) where
      field _<_ : X → X → Type 𝓊

    ⟪⊂⟫ : (X : ℙ $ ℙ A) → Lt ⟪ X ⟫
    ⟪⊂⟫ X = record { _<_ = λ (x , _) (y , _) → x ⊂ y }

  ℍ→ℙ³-inj : injective ℍ→ℙ³
  ℍ→ℙ³-inj = {!   !}

