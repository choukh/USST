---
title: 泛等结构集合论 (4) 序数的序
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
---

# 泛等结构集合论 (4) 序数的序

> 交流Q群: 893531731  
> 本文源码: [Ordinal.Order.lagda.md](https://github.com/choukh/USST/blob/main/src/Ord/Order.lagda.md)  
> 高亮渲染: [Ordinal.Order.html](https://choukh.github.io/USST/Ord.Order.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --hidden-argument-puns #-}
module Ordinal.Order where
open import Preliminary
open import Ordinal.Base
```

## 序数模仿

我们说序数底集间的一个映射是序数间的一个模仿 (简称序数模仿), 当且仅当它保序, 且它的像能形成一个前段.

```agda
record IsSimulation {α : Ord ℓ} {β : Ord ℓ′} (f : ⟨ α ⟩ → ⟨ β ⟩) : Type (ℓ ⊔ ℓ′) where
  module ₁ = OrdStr (str α)
  module ₂ = OrdStr (str β)
```

保序性 `pres<` 很简单, 它就是上一章同伦保序 `hPres<` 的弱化版. "形成前段" 即 `formsInitSeg` 这一性质的直观可以参考下图. 它说只要一个底集元素被射到, 那么比它小的元素都会被射到, 也就是映射的像能形成 `<` 的一个前段.

... a   ... <₁ ... a′  ...
    |              |
  f |            f |
    ↓              ↓
... f a ... <₂ ... f a′ ...

```agda
  field
    pres< : ∀ a a′ → a ₁.< a′ → f a ₂.< f a′
    formsInitSeg : ∀ b a′ → b ₂.< f a′ → Σ[ a ∈ ⟨ α ⟩ ] a ₁.< a′ × f a ≡ b
```

**引理** 序数模仿是单射.

```agda
simulation-inj :(f : ⟨ α ⟩ → ⟨ β ⟩) → IsSimulation f → injective f
simulation-inj {α} {β} f f-sim = {!   !}
  where
  open IsSimulation f-sim
  open OrdStr (str α) renaming (_<_ to _<₁_) using (<-ext)
  open OrdStr (str β) renaming (_<_ to _<₂_) using ()
  open BinaryRelation _<₁_ using (Acc; acc)

  Acc→inj : ∀ x y → Acc x → Acc y → f x ≡ f y → x ≡ y
  Acc→inj x y (acc H₁) (acc H₂) fx≡fy = <-ext x y λ z → p z , q z
    where
    p : ∀ z → z <₁ x → z <₁ y
    p z z<x = {!   !}
      where
      fz<fy : f z <₂ f y
      fz<fy = {! transport   !}
    q : ∀ z → z <₁ y → z <₁ x
    q z z<y = {!   !}
```
