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
module Ordinal.Order where
open import Preliminary
open import Ordinal.Base
```

## 序数间模仿

我们说序数底集间的一个映射是序数间的一个模仿 (简称序数模仿), 当且仅当它保序, 且它的像能形成一个前段.

```agda
record isSimulation {α β : Ord ℓ} (f : ⟨ α ⟩ → ⟨ β ⟩) : Type ℓ where
  module ₁ = OrdStr (str α)
  module ₂ = OrdStr (str β)
```

保序性 `pres<` 很简单, 它就是上一章同伦保序 `hPres<` 的弱化版. 形成前段这一性质 `formsInitSeg` 可以参考下图. 它是说只要一个底集元素被射到, 那么比它小的元素都会被射到, 也就是映射的像能形成 `<` 的一个前段.

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
  --simulation-inj : {α β : Ord ℓ} (f : ⟨ α ⟩ → ⟨ β ⟩) → ∀ a a′ → f a ≡ f a′ → a ≡ a′
```
