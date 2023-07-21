---
title: 泛等结构集合论 (4) 序数的序
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
zhihu-url: https://zhuanlan.zhihu.com/p/644984990
---

# 泛等结构集合论 (4) 序数的序

> 交流Q群: 893531731  
> 本文源码: [Ordinal.Order.lagda.md](https://github.com/choukh/USST/blob/main/src/Ordinal/Order.lagda.md)  
> 高亮渲染: [Ordinal.Order.html](https://choukh.github.io/USST/Ordinal.Order.html)  

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

## 序数嵌入

我们说序数底集间的一个映射是序数嵌入, 当且仅当它保序, 且它的像能形成一个前段.

```agda
record IsOrdEmbed {α : Ord 𝓊} {β : Ord 𝓋} (f : ⟨ α ⟩ → ⟨ β ⟩) : Type (𝓊 ⊔ 𝓋) where
  constructor mkIsOrdEmbed
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

**引理** 序数嵌入是单射.  
**证明** 用双参数形式的良基归纳法 `elim2`, 拿到归纳假设 `IH : ∀ u v → u ≺ x → v ≺ y → f u ＝ f v → u ＝ v`, 要证 `f x ＝ f y → x ＝ y`. 用 `≺` 的外延性, 要证两种对称的情况 `p` 和 `q`, 我们只证 `p : ∀ z → z ≺ x → z ≺ y`. 由 `z ≺ x` 及嵌入的保序性有 `f z ≺ f x ≡ f y`. 由于嵌入能形成前段, 必有一个 `w` 满足 `w ≺ y` 且 `f w ＝ f z`. 再结合归纳假设有 `w ＝ z`, 改写目标即证 `w ≺ y`, 此乃前提. ∎

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
**证明** 由于前段性是命题, 只需证 `b` 对应的 `α` 前段唯一. 假设有两个这样的前段, 分别有端点 `x` 和 `y` 被 `f` 射到 `b`, 由嵌入的单射性 `x ＝ y`. ∎

```agda
  isPropFormsInitSeg : ∀ b a′ → b ≺⟨ β ⟩ f a′ → isProp (Σ a ∶ ⟨ α ⟩ , (a ≺⟨ α ⟩ a′) × (f a ＝ b))
  isPropFormsInitSeg b a′ b≺fa′ (x , x≺a′ , fx＝b) (y , y≺a′ , fy＝b) = eqToPath $ Σ≡Prop
    (λ _ → isPropPathToIsProp $ isProp× (≺-prop _ _) (transportIsProp $ underlying-set _ _))
    (inj (fx＝b ∙ sym fy＝b))
    where
    open OrdStr (str α) using (≺-prop)
    open OrdStr (str β) using (underlying-set)
```

于是嵌入性是命题.

```agda
isPropIsOrdEmbed : {α : Ord 𝓊} {β : Ord 𝓋} (f : ⟨ α ⟩ → ⟨ β ⟩) → isProp (IsOrdEmbed f)
isPropIsOrdEmbed {α} {β} f = isOfHLevelRetractFromIso 1 IsOrdEmbedIsoΣ $ aux
  where
  unquoteDecl IsOrdEmbedIsoΣ = declareRecordIsoΣ IsOrdEmbedIsoΣ (quote IsOrdEmbed)
  aux : ∀ x y → x ≡ y
  aux x _ = ΣPathP (isPropΠ3 isPropPres≺ _ _ , isPropΠ3 isPropFormsInitSeg _ _)
    where open IsOrdEmbed {α = α} {β} (Iso.inv IsOrdEmbedIsoΣ x)
```

### 唯一性

**引理** 给定两个序数, 它们之间的嵌入唯一.  
**证明** 用函数的外延性以及底序的外延性, 使用与嵌入的单射性的证明类似的改写即证. ∎

```
ordEmbed-unique : {α : Ord 𝓊} {β : Ord 𝓊′}
  (f g : ⟨ α ⟩ → ⟨ β ⟩) → IsOrdEmbed f → IsOrdEmbed g → f ＝ g
ordEmbed-unique {α} {β} f g f-ordEmb g-ordEmb =
  funExt $ elim λ x IH → ≺-ext (f x) (g x) λ z →
    (λ z≺fx → let (a , a≺x , fa＝z) = formsInitSeg f-ordEmb z x z≺fx in
      transport (_≺ g x) (sym (IH a a≺x) ∙ fa＝z) (pres≺ g-ordEmb a x a≺x))
  , (λ z≺gx → let (a , a≺x , ga＝z) = formsInitSeg g-ordEmb z x z≺gx in
      transport (_≺ f x) (IH a a≺x ∙ ga＝z) (pres≺ f-ordEmb a x a≺x))
  where open IsOrdEmbed
        open OrdStr (str α) using (elim)
        open OrdStr (str β) using (≺-ext; _≺_)
```

**引理** 序数等价也是一个序数嵌入.  
**证明** 要证序数等价的底层函数 `f` 保序且形成前段. 保序性即 `hPres≺` 的底层函数. 对任意 `b ≺ f a′`, 有 `f (f⁻¹ b) ＝ b`, 改写可得 `f (f⁻¹ b) ≺ f a′`, 再用 `hPres≺⁻¹` 即得 `(f⁻¹ b) ≺ a′`. 于是 `f⁻¹ b` 就是"形成前段"条件所要求的 `a`. ∎

```agda
IsOrdEquiv→IsOrdEmbed : (f : ⟨ α ⟩ ≃ ⟨ β ⟩) → IsOrdEquiv (str α) f (str β) → IsOrdEmbed (f ⁺¹)
IsOrdEquiv→IsOrdEmbed {β} f ordEquiv = mkIsOrdEmbed
  (λ a a′ → hPres≺ a a′ ⁺¹)
  (λ b a′ b≺fa′ → (f ⁻¹) b
    , (hPres≺ _ a′ ⁻¹) (transport (λ - → - ≺⟨ β ⟩ _) (sym $ secEq f b) b≺fa′)
    , secEq f b)
  where open IsOrdEquiv ordEquiv
```

**引理** 给定两个序数, 它们之间的序数等价唯一.  
**证明** 由于"是序数等价"是命题, 只需证该等价的底层函数唯一. 又序数等价也是序数嵌入, 由序数嵌入的唯一性得证. ∎

```agda
isPropOrdEquiv : (α : Ord 𝓊) (β : Ord 𝓊′) → isProp (α ≃ₒ β)
isPropOrdEquiv α β (f , f-ordEquiv) (g , g-ordEquiv) = eqToPath $ Σ≡Prop
  (λ _ → isPropPathToIsProp $ isPropIsOrdEquiv _ _ _)
  (equivEq $ ordEmbed-unique (f ⁺¹) (g ⁺¹)
    (IsOrdEquiv→IsOrdEmbed f f-ordEquiv)
    (IsOrdEquiv→IsOrdEmbed g g-ordEquiv))
```

**推论** 序数宇宙是集合.  
**证明** 即证两个序数的相等是命题, 由序数的泛等原理, 这等价于证两个序数间的等价唯一. ∎

```agda
isSetOrd : isSet (Ord 𝓊)
isSetOrd α β = (equiv ⁺¹) (isOfHLevelLift 1 $ isPropOrdEquiv α β)
  where
  equiv : isProp (Lift (α ≃ₒ β)) ≃ isProp (α ≡ β)
  equiv = cong≃ isProp $ compEquiv (invEquiv LiftEquiv) (OrdinalPath α β)
```

## 序数的序

序数之间的序 `_≤_` 定义为它们之间的嵌入的全体.

```agda
_≤_ : Ord 𝓊 → Ord 𝓋 → Type (𝓊 ⊔ 𝓋)
α ≤ β = Σ (⟨ α ⟩ → ⟨ β ⟩) IsOrdEmbed
```

因为嵌入是唯一的, 所以 `_≤_` 是命题.

```agda
≤-prop : (α : Ord 𝓊) (β : Ord 𝓋) → isProp (α ≤ β)
≤-prop α β (f , f-ordEmb) (g , g-ordEmb) = eqToPath $ Σ≡Prop
  (isPropPathToIsProp ∘ isPropIsOrdEmbed)
  (ordEmbed-unique f g f-ordEmb g-ordEmb)
```
