---
title: 泛等结构集合论 (4) 序数模仿
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
---

# 泛等结构集合论 (4) 序数模仿

> 交流Q群: 893531731  
> 本文源码: [Simulation.Order.lagda.md](https://github.com/choukh/USST/blob/main/src/Ordinal/Simulation.lagda.md)  
> 高亮渲染: [Simulation.Order.html](https://choukh.github.io/USST/Ordinal.Simulation.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification --hidden-argument-puns #-}
module Ordinal.Simulation where
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

### 单射性

**引理** 序数模仿是单射.  
**证明** 用双参数形式的良基归纳法 `elim2`, 拿到归纳假设 `IH : ∀ u v → u ≺ x → v ≺ y → f u ＝ f v → u ＝ v`, 要证 `f x ＝ f y → x ＝ y`. 用 `≺` 的外延性, 要证两种对称的情况 `p` 和 `q`, 我们只证 `p : ∀ z → z ≺ x → z ≺ y`. 由 `z ≺ x` 及模仿的保序性有 `f z ≺ f x ≡ f y`. 由于模仿能形成前段, 必有一个 `w` 满足 `w ≺ y` 且 `f w ＝ f z`. 再结合归纳假设有 `w ＝ z`, 改写目标即证 `w ≺ y`, 此乃前提. ∎

```agda
  inj : injective f
  inj = elim2 aux _ _
    where
    open OrdStr (str α) using (≺-ext; elim2)

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

### 命题性

易证保序性是命题.

```agda
  isPropPres≺ : ∀ a a′ → a ≺⟨ α ⟩ a′ → isProp (f a ≺⟨ β ⟩ f a′)
  isPropPres≺ _ _ _ = ≺-prop _ _
    where open OrdStr (str β) using (≺-prop)
```

**引理** "形成前段"是命题, 尽管没有截断.
**证明** 由于前段性是命题, 只需证 `b` 对应的 `α` 前段唯一. 假设有两个这样的前段, 分别有端点 `x` 和 `y` 被 `f` 射到 `b`, 由模仿的单射性 `x ＝ y`. ∎

```agda
  isPropFormsInitSeg : ∀ b a′ → b ≺⟨ β ⟩ f a′ → isProp (Σ a ∶ ⟨ α ⟩ , (a ≺⟨ α ⟩ a′) × (f a ＝ b))
  isPropFormsInitSeg b a′ b≺fa′ (x , x≺a′ , fx＝b) (y , y≺a′ , fy＝b) = eqToPath $ Σ≡Prop
    (λ a → isPropPathToIsProp $ isProp× (≺-prop _ _) (transportIsProp $ underlying-set _ _))
    (inj (fx＝b ∙ sym fy＝b))
    where
    open OrdStr (str α) using (≺-prop)
    open OrdStr (str β) using (underlying-set)
```

于是模仿性是命题.

```agda
unquoteDecl IsSimulationIsoΣ = declareRecordIsoΣ IsSimulationIsoΣ (quote IsSimulation)

isPropIsSimulation : {α : Ord 𝓊} {β : Ord 𝓋} (f : ⟨ α ⟩ → ⟨ β ⟩) → isProp (IsSimulation f)
isPropIsSimulation {α} {β} f = isOfHLevelRetractFromIso 1 IsSimulationIsoΣ $ aux where
  aux : ∀ x y → x ≡ y
  aux x _ = ΣPathP (isPropΠ3 isPropPres≺ _ _ , isPropΠ3 isPropFormsInitSeg _ _)
    where open IsSimulation {α = α} {β} (Iso.inv IsSimulationIsoΣ x)
```

```agda
Simulation : Ord 𝓊 → Ord 𝓋 → Type (𝓊 ⊔ 𝓋)
Simulation α β = Σ (⟨ α ⟩ → ⟨ β ⟩) IsSimulation
```

### 唯一性

**引理** 给定两个序数, 它们之间的模仿是唯一的.  
**证明** TODO ∎

```agda
isPropSimulation : ∀ α β → isProp (Simulation {𝓊} {𝓋} α β)
isPropSimulation α β (f , f-sim) (g , g-sim) = eqToPath $ Σ≡Prop
  (isPropPathToIsProp ∘ isPropIsSimulation)
  (funExt $ elim λ x IH → ≺-ext (f x) (g x) λ z →
    (λ z≺fx → let (a , a≺x , fa＝z) = formsInitSeg f-sim z x z≺fx in
      transport (_≺ g x) (sym (IH a a≺x) ∙ fa＝z) (pres≺ g-sim a x a≺x))
  , (λ z≺gx → let (a , a≺x , ga＝z) = formsInitSeg g-sim z x z≺gx in
      transport (_≺ f x) (IH a a≺x ∙ ga＝z) (pres≺ f-sim a x a≺x)))
  where open IsSimulation
        open OrdStr (str α) using (elim)
        open OrdStr (str β) using (≺-ext; _≺_)
```
