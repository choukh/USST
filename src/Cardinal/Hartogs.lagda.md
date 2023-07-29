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
open import Ordinal
open BinaryRelation
```

```agda
module Pre {A : Type 𝓊} (A-set : isSet A) where
```

  ℍ : Ord (𝓊 ⁺)
  ℍ = ?
