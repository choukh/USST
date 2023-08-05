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
open import Ordinal renaming (_≤_ to _≤ₒ_)
open BinaryRelation
```

```agda
Card : (𝓊 : Level) → Type (𝓊 ⁺)
Card 𝓊 = ∥ hSet 𝓊 ∥₂
```

```agda
_≤ₕ_ : Card 𝓊 → Card 𝓋 → hProp (𝓊 ⊔ 𝓋)
_≤ₕ_ = ∥∥₂-rec2 isSetHProp λ (A , _) (B , _) → ∥ A ≲ B ∥₁ , squash₁
```

```agda
_≤_ : Card 𝓊 → Card 𝓋 → Type (𝓊 ⊔ 𝓋)
κ ≤ μ = ⟨ κ ≤ₕ μ ⟩

isProp≤ : (κ : Card 𝓊) (μ : Card 𝓋) → isProp (κ ≤ μ)
isProp≤ κ μ = str (κ ≤ₕ μ)
```


module Pre {A : Type 𝓊} (A-set : isSet A) where

  hartogs : EmbeddedOrd (𝓊 ⁺)
  EmbeddedOrd.carrier       hartogs = Σ (B , strB) ∶ Ord 𝓊 , ∣ B , OrdStr.underlying-set strB ∣₂ ≤ ∣ A , A-set ∣₂
  EmbeddedOrd._≺_           hartogs = {!   !}
  EmbeddedOrd.relation-prop hartogs = {!   !}
  EmbeddedOrd.target        hartogs = {!   !}
  EmbeddedOrd.embed         hartogs = {!   !}
  EmbeddedOrd.inj           hartogs = {!   !}
  EmbeddedOrd.pres≺         hartogs = {!   !}
  EmbeddedOrd.formsInitSeg  hartogs = {!   !}

  ℍ : Ord (𝓊 ⁺)
  ℍ = tieup hartogs

