---
title: 泛等结构集合论 (3) 序数
zhihu-tags: Agda, 数理逻辑, 集合论
zhihu-url: https://zhuanlan.zhihu.com/p/643217740
---

# 泛等结构集合论 (3) 序数

> 交流Q群: 893531731  
> 本文源码: [Ordinals.lagda.md](https://github.com/choukh/USST/blob/main/src/Ordinals.lagda.md)  
> 高亮渲染: [Ordinals.html](https://choukh.github.io/USST/Ordinals.html)  

我们导入前置知识, 并全局假设 `PR`. 本讲将复刻质料集合论的重要概念: 序数.

```agda
{-# OPTIONS --cubical --safe #-}
open import Preliminary
module Ordinals ⦃ _ : PR ⦄ where
```