---
title: 泛等结构集合论 (3) 序数的定义
zhihu-tags: Agda, 数理逻辑, 集合论
---

# 泛等结构集合论 (3) 序数的定义

> 交流Q群: 893531731  
> 本文源码: [Base.lagda.md](https://github.com/choukh/USST/blob/main/src/Ordinal/Base.lagda.md)  
> 高亮渲染: [Base.html](https://choukh.github.io/USST/Ordinal.Base.html)  

我们导入前置知识, 并全局假设 `PR`. 本讲将复刻质料集合论的重要概念: 序数.

```agda
{-# OPTIONS --cubical --safe #-}
open import Preliminary
module Ordinal.Base ⦃ _ : PR ⦄ where
```

## 序关系的一些性质

说白了, 一个序数就是由一个集合以及该集合上的一个满足一定性质的序关系所组成的结构. 我们先定义这个序关系需要满足的性质.

给定类型 `A : Type ℓ` 及其上的序关系 `_<_ : A → A → Type ℓ′`

```agda
module _ {A : Type ℓ} (_<_ : A → A → Type ℓ′) where
```

### 命题性

我们说 `_<_` 是一个 **命题 (propositional)** 关系, 当且仅当对任意 `x y : A`, `x < y` 是一个命题.

```agda
  Propositional : Type _
  Propositional = ∀ x y → isProp (x < y)
```

命题性本身是一个命题.

```agda
  _ : isProp Propositional
  _ = isPropΠ2 λ _ _ → isPropIsProp
```

### 反自反性

我们说 `_<_` 是一个 **反自反 (irreflexive)** 关系, 当且仅当对任意 `x : A`, `x ≮ x`.

```agda
  _≮_ : A → A → Type ℓ′
  x ≮ y = ¬ x < y

  Irreflexive : Type _
  Irreflexive = ∀ x → x ≮ x
```

反自反性是一个命题.

```agda
  isPropIrreflexive : isProp Irreflexive
  isPropIrreflexive = isPropΠ2 λ _ _ → isProp⊥
```

### 传递性

我们说 `_<_` 是一个 **传递 (transitive)** 关系, 当且仅当对任意 `x y z : A`, `x < y` 与 `y < z` 蕴含 `x < z`.

```agda
  Transitive : Type _
  Transitive = ∀ x y z → x < y → y < z → x < z
```

如果`_<_` 是一个命题关系, 那么传递性是一个命题.

```agda
  isPropTransitive : Propositional → isProp Transitive
  isPropTransitive prop = isPropΠ5 λ _ _ _ _ _ → prop _ _
```

## 外延性

我们说 `_<_` 是一个 **外延 (extensional)** 关系, 当且仅当对任意 `x y : A`, 如果对任意 `z : A` 都有 `z < x` 当且仅当 `z < y`, 那么 `x ≡ y`.

```agda
  Extensional : Type _
  Extensional = ∀ x y → (∀ z → z < x ↔ z < y) → x ≡ y
```

如果 `A` 是集合, 那么外延性是命题.

```agda
  isPropExtensional : isSet A → isProp Extensional
  isPropExtensional A-set = isPropΠ3 λ _ _ _ → transportIsProp $ A-set _ _
```

### 良基性

我们说在 `_<_` 关系下, 一个 `x : A` **可及 (accessible)**, 当且仅当对任意 `y < x`, `y` 也可及.

```agda
  data Acc (x : A) : Type (ℓ ⊔ ℓ′) where
    acc : (∀ y → y < x → Acc y) → Acc x
```

我们说 `_<_` 是一个 **良基 (well-founded)** 关系, 当且仅当任意 `x : A` 都可及.

```agda
  WellFounded : Type _
  WellFounded = ∀ x → Acc x
```

可及性是一个命题. 下面的证明中暴露了 cubical 的底层机制, 就是那个 `i`, 以使证明更简洁. 也可以不暴露, 只需证 `H₁` 等于 `H₂`, 它们都具有 `∀ y → y < x → Acc y` 类型. 由归纳假设, `Acc y` 是命题, 所以这个Π类型也是命题, 所以它的两个项 `H₁` 与 `H₂` 相等.

```agda
  isPropAcc : ∀ x → isProp (Acc x)
  isPropAcc x (acc H₁) (acc H₂) i = acc λ y y<x → isPropAcc y (H₁ y y<x) (H₂ y y<x) i
```

良基性也是一个命题.

```agda
  isPropWellFounded : isProp WellFounded
  isPropWellFounded = isPropΠ λ _ → isPropAcc _
```

良基性蕴含反自反性. 只需证对任意可及的 `x` 都有 `x ≮ x`, 显然成立.

```agda
  Acc→Irreflexive : ∀ x → Acc x → x ≮ x
  Acc→Irreflexive x (acc H) x<x = Acc→Irreflexive x (H x x<x) x<x

  WellFounded→Irreflexive : WellFounded → Irreflexive
  WellFounded→Irreflexive wf x = Acc→Irreflexive x (wf x)
```

## 序数性

我们说类型 `A` 和其上的序关系 `_<_` 构成一个 **序数 (ordinal)**, 记作 `IsOrdinal A _<_`, 当且仅当它们满足: `A` 是集合且 `_<_` 有命题性, 传递性, 外延性和良基性. 因为良基性蕴含反自反性, 所以 `_<_` 也有反自反性.

```agda
record IsOrdinal (A : Type ℓ) (_<_ : A → A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  field
    ord-set   : isSet A
    <-prop    : Propositional _<_
    <-trans   : Transitive _<_
    <-ext     : Extensional _<_
    <-wf      : WellFounded _<_

  <-irrefl : Irreflexive _<_
  <-irrefl = WellFounded→Irreflexive _<_ <-wf
```

由于序数性里面的每个条件都是命题, 所以序数性也是一个命题.

```agda
unquoteDecl IsOrdinalIsoΣ = declareRecordIsoΣ IsOrdinalIsoΣ (quote IsOrdinal)

isPropIsOrdinal : (A : Type ℓ) (_<_ : A → A → Type ℓ′) → isProp (IsOrdinal A _<_)
isPropIsOrdinal A _<_ = isOfHLevelRetractFromIso 1 IsOrdinalIsoΣ $
  isPropΣ (isPropΠ2 λ _ _ → isPropIsProp) λ ord-set →
  isPropΣ (isPropΠ2 λ _ _ → isPropIsProp) λ <-prop → isProp×2
    (isPropTransitive _ <-prop)
    (isPropExtensional _ ord-set)
    (isPropWellFounded _)
```

一个类型 `A` 配备上满足序数性的序关系 `_<_` 就构成了一个序数结构 `OrdianlStr`.

```agda
record OrdianlStr (ℓ′ : Level) (A : Type ℓ) : Type (ℓ ⊔ ℓ-suc ℓ′) where
  field
    _<_ : A → A → Type ℓ′
    isOrdinal : IsOrdinal A _<_
  open IsOrdinal isOrdinal public
```

序数宇宙 `Ordinal` 定义为类型宇宙配备上序数结构.

```agda
Ordinal : (ℓ ℓ′ : Level) → Type _
Ordinal ℓ ℓ′ = TypeWithStr ℓ (OrdianlStr ℓ′)
```
