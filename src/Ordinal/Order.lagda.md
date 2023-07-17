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
{-# OPTIONS --lossy-unification --hidden-argument-puns #-}
module Ordinal.Order where
open import Preliminary
open import Ordinal.Base
```

## 底序

以下一大块代码都仅仅是为了定义出 `x ≺⟨ α ⟩ y` 的写法. 其中 `≺⟨ α ⟩` 叫做 `α` 的底序, 与底集相对应, 它们共同组成了一个序数的底层结构.

```agda
record Underlying {𝓊} (O : Type (𝓊 ⁺)) : Type (𝓊 ⁺) where
  field
    underlyingSet : O → Type 𝓊
    underlyingRel : (α : O) → underlyingSet α → underlyingSet α → Type 𝓊
  syntax underlyingRel α x y = x ≺⟨ α ⟩ y

open Underlying ⦃...⦄ public

instance
  underlying : Underlying (Ord 𝓊)
  underlyingSet ⦃ underlying ⦄ = ⟨_⟩
  underlyingRel ⦃ underlying ⦄ = OrdStr._≺_ ∘ str
```

## 序数模仿

我们说序数底集间的一个映射是序数间的一个模仿 (简称序数模仿), 当且仅当它保序, 且它的像能形成一个前段.

```agda
record IsSimulation {α : Ord 𝓊} {β : Ord 𝓋} (f : ⟨ α ⟩ → ⟨ β ⟩) : Type (𝓊 ⊔ 𝓋) where
```

保序性 `pres≺` 很简单, 它就是上一章同伦保序 `hPres≺` 的弱化版. "形成前段" `formsInitSeg` 这一性质的直观可以参考下图. 它说只要一个底集元素被射到, 那么比它小的元素都会被射到, 也就是映射的像能形成 `≺` 的一个前段.

... a   ... ≺₁ ... a′  ...
    |              |
  f |            f |
    ↓              ↓
... f a ... ≺₂ ... f a′ ...

```agda
  field
    pres≺ : ∀ a a′ → a ≺⟨ α ⟩ a′ → f a ≺⟨ β ⟩ f a′
    formsInitSeg : ∀ b a′ → b ≺⟨ β ⟩ f a′ → Σ a ∶ ⟨ α ⟩ , a ≺⟨ α ⟩ a′ × f a ＝ b
```

**引理** 序数模仿是单射.  
**证明梗概** 用双参数形式的良基归纳法 `wf-elim2`, 拿到归纳假设 `IH : ∀ u v → u ≺ x → v ≺ y → f u ＝ f v → u ＝ v`, 要证 `f x ＝ f y → x ＝ y`. 用 `≺` 的外延性, 要证两种对称的情况 `p` 和 `q`, 我们只证 `p : ∀ z → z ≺ x → z ≺ y`. 由 `z ≺ x` 及模仿的保序性有 `f z ≺ f x ≡ f y`. 由于模仿能形成前段, 必有一个 `w` 满足 `w ≺ y` 且 `f w ＝ f z`. 再结合归纳假设有 `w ＝ z`, 改写目标即证 `w ≺ y`, 此乃前提. ∎

```agda
simulation-inj :(f : ⟨ α ⟩ → ⟨ β ⟩) → IsSimulation f → injective f
simulation-inj {α} {β} f f-sim = wf-elim2 ≺-wf aux _ _
  where
  open BinaryRelation (underlyingRel α) using (wf-elim2)
  open OrdStr (str α) using (≺-ext; ≺-wf)
  open IsSimulation f-sim using (pres≺; formsInitSeg)

  aux : ∀ x y → (∀ u v → u ≺⟨ α ⟩ x → v ≺⟨ α ⟩ y → f u ＝ f v → u ＝ v) → f x ＝ f y → x ＝ y
  aux x y IH fx＝fy = ≺-ext x y λ z → p z , q z
    where
    p : ∀ z → z ≺⟨ α ⟩ x → z ≺⟨ α ⟩ y
    p z z≺x = transport (λ - → - ≺⟨ α ⟩ y) w≡z w≺y
      where
      fz≺fy : f z ≺⟨ β ⟩ f y
      fz≺fy = transport (λ - → f z ≺⟨ β ⟩ -) fx＝fy (pres≺ z x z≺x)
      Σw : Σ w ∶ ⟨ α ⟩ , (w ≺⟨ α ⟩ y × f w ＝ f z)
      Σw = formsInitSeg (f z) y fz≺fy
      w = fst Σw
      w≺y = fst $ snd Σw
      fw＝fz = snd $ snd Σw
      w≡z : w ＝ z
      w≡z = sym $ IH z w z≺x w≺y (sym fw＝fz)
    q : ∀ z → z ≺⟨ α ⟩ y → z ≺⟨ α ⟩ x
    q z z≺y = transport (λ - → - ≺⟨ α ⟩ x) w≡z w≺x
      where
      fz≺fx : f z ≺⟨ β ⟩ f x
      fz≺fx = transport (λ - → f z ≺⟨ β ⟩ -) (sym fx＝fy) (pres≺ z y z≺y)
      Σw : Σ w ∶ ⟨ α ⟩ , (w ≺⟨ α ⟩ x × f w ＝ f z)
      Σw = formsInitSeg (f z) x fz≺fx
      w = fst Σw
      w≺x = fst $ snd Σw
      fw＝fz = snd $ snd Σw
      w≡z : w ＝ z
      w≡z = IH w z w≺x z≺y fw＝fz
```
