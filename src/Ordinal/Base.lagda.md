---
title: 泛等结构集合论 (3) 序数的定义及其泛等原理
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
zhihu-url: https://zhuanlan.zhihu.com/p/643453391
---

# 泛等结构集合论 (3) 序数的定义及其泛等原理

> 交流Q群: 893531731  
> 本文源码: [Ordinal.Base.lagda.md](https://github.com/choukh/USST/blob/main/src/Ord/Base.lagda.md)  
> 高亮渲染: [Ordinal.Base.html](https://choukh.github.io/USST/Ord.Base.html)  

本章将复刻质料集合论的重要概念: 序数.

```agda
{-# OPTIONS --cubical --safe #-}
module Ordinal.Base where
open import Preliminary
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
  isPropPropositional : isProp Propositional
  isPropPropositional = isPropΠ2 λ _ _ → isPropIsProp
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

### 外延性

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

**引理** 如果 `_<_` 同时具有命题性和外延性那么 `A` 是集合.
**证明梗概** 由引理 `Collapsible≡→isSet`, 只要证明 `A` 上的相等类型 `x ≡ y` 可折叠, 就证明了 `A` 是集合. 可折叠是说能构造 `x ≡ y` 的自映射 `f` 满足 `f` 是一个常函数. 只要用作为自变量的那个 `eq : x ≡ y` 替换外延性的前提 `z < x ↔ z < y` 就能得到另一个 `x ≡ y`. 由于 `_<_` 是命题, 所以 `z < x ↔ z < y` 是命题, 所以 `f` 是常函数. ∎

```agda
  open import Cubical.Foundations.Function using (2-Constant)
  open import Cubical.Relation.Nullary using (Collapsible; Collapsible≡→isSet)

  Extensional→isSet : Propositional → Extensional → isSet A
  Extensional→isSet prop ext = Collapsible≡→isSet λ x y →
    transport Collapsible (sym Path≡Eq) $ collapser x y , didCollapse x y
    where
    collapser : ∀ x y → x ≡ y → x ≡ y
    collapser x y eq = ext x y λ z → (transport (z <_) eq) , (transport (z <_) (sym eq))
    didCollapse : ∀ x y → 2-Constant (collapser x y)
    didCollapse x y p q = eqToPath $ ap (ext x y) $ funExt λ _ → Σ≡Prop
      (λ _ _ _ → pathToEq $ isProp→ (prop _ _) _ _)
      (funExt λ _ → pathToEq $ prop _ _ _ _)
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

可及性是一个命题. 下面的证明中暴露了 cubical 的底层机制, 就是那个间点 `i`, 以使证明更简洁. 也可以不暴露, 只需证 `H₁` 等于 `H₂`, 它们都具有 `∀ y → y < x → Acc y` 类型. 由归纳假设, `Acc y` 是命题, 所以这个Π类型也是命题, 所以它的两个项 `H₁` 与 `H₂` 相等.

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

### 良序性

我们说 `_<_` 是一个 **良序 (well-ordered)** 关系, 当且仅当: `_<_` 有命题性, 传递性, 外延性和良基性.

```agda
  record WellOrdered : Type (ℓ ⊔ ℓ′) where
    constructor mkWellOrdered
    field
      <-prop    : Propositional
      <-trans   : Transitive
      <-ext     : Extensional
      <-wf      : WellFounded
```

良序关系是反自反的, 且其基底类型必是集合, 我们今后称之为**底集 (underlying set)**. 经典数学里面一般是把这里的外延性换成了三歧性, 但在直觉主义中外延性更容易处理. 此外, HoTT Book 也有相应的定义, 见 Def 10.3.17, 它要求 "`A` 是集合", 但这不是必须的, Escardó 首先证明了[这一点](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Ordinals.Notions.html#8277)

```agda
    <-irrefl : Irreflexive
    <-irrefl = WellFounded→Irreflexive <-wf

    underlying-set : isSet A
    underlying-set = Extensional→isSet <-prop <-ext
```

由于良序性里面的每个条件都是命题, 所以良序性也是一个命题.

```agda
  unquoteDecl WellOrderedIsoΣ = declareRecordIsoΣ WellOrderedIsoΣ (quote WellOrdered)

  isPropWellOrdered : isProp WellOrdered
  isPropWellOrdered = isOfHLevelRetractFromIso 1 WellOrderedIsoΣ $ aux where
    aux : ∀ x y → Path x y
    aux x _ = ΣPathP (isPropPropositional _ _
            , ΣPathP (isPropTransitive <-prop _ _
            , ΣPathP (isPropExtensional underlying-set _ _
            , isPropWellFounded _ _)))
      where open WellOrdered (Iso.inv WellOrderedIsoΣ x)
```

## 序数的定义

为了方便 `𝒮ᴰ-Record` 宏处理, 我们遵循 cubical 库的做法, 先用 record 类型定义序数结构, 然后用Σ类型把序数定义为类型宇宙配备上序数结构.

### 序数结构

一个类型 `A` 配备上满足良序关系的 `_<_` 就构成了一个序数结构 `OrdStr`. 注意我们这里让 `_<_` 与底集 `A` 居留于同一宇宙, 这可以让形式更简单, 反正 `_<_` 是命题, 而我们有 `PR` 可以随时调整命题宇宙.

```agda
record OrdStr (A : Type ℓ) : Type (ℓ-suc ℓ) where
  constructor mkOrdinalStr
  field
    _<_ : A → A → Type ℓ
    <-wo : WellOrdered _<_
  open WellOrdered <-wo public
```

### 序数宇宙

类型宇宙配备上序数结构就构成了序数宇宙 `Ord`. 注意 `Ord` 后面跟的 `ℓ` 指的是底集所在的宇宙, 而 `Ord` 本身位于 `ℓ-suc ℓ` 宇宙.

```agda
Ord : (ℓ : Level) → Type (ℓ-suc ℓ)
Ord ℓ = TypeWithStr ℓ OrdStr
```

## 序数等价

序数间的同伦等价 `α ≃ₒ β` 定义为保持序关系的底集间同伦等价 `A ≃ B`. 注意"保持序关系"也必须用同伦等价来表达, 即对任意 `x y : A` 有 `x <₁ y` 与 `f x <₂ f y` 同伦等价, 其中 `<₁` 和 `<₂` 分别是 `A` 和 `B` 上的序关系, `f` 是 `A ≃ B` 的底层函数.

```agda
record IsOrdEquiv {A : Type ℓ₁} {B : Type ℓ₂}
  (a : OrdStr A) (e : A ≃ B) (b : OrdStr B) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor mkIsOrderEquiv
  private
    module ₁ = OrdStr a
    module ₂ = OrdStr b
    f = equivFun e
  field
    pres< : (x y : A) → x ₁.< y ≃ f x ₂.< f y

_≃ₒ_ : Ord ℓ₁ → Ord ℓ₂ → Type _
α ≃ₒ β = Σ[ e ∈ ⟨ α ⟩ ≃ ⟨ β ⟩ ] IsOrdEquiv (str α) e (str β)
```

## 序数的泛等原理

接下来就是使用 `𝒮ᴰ-Record` 得到序数的泛等原理. 不需要深究其语法, 只需认为它是一种 boilerplate (样板代码), 在 cubical 的代数模块里面也被大量使用. 总之我们用 `𝒮ᴰ-Record` 拿到了 `𝒮ᴰ-Ord : DUARel ...` 这一串东西.

```agda
𝒮ᴰ-Ord : DUARel (𝒮-Univ ℓ) OrdStr ℓ
𝒮ᴰ-Ord = 𝒮ᴰ-Record (𝒮-Univ _) IsOrdEquiv
  (fields:
    data[ _<_ ∣ autoDUARel _ _ ∣ pres< ]
    prop[ <-wo ∣ (λ _ _ → isPropWellOrdered _) ])
  where
  open OrdStr
  open IsOrdEquiv
```

然后就可以用 `∫` 从 `𝒮ᴰ-Ord` 中取出序数的泛等原理: 两个序数的等价等价于它们的相等.

```agda
OrdinalPath : (α β : Ord ℓ) → (α ≃ₒ β) ≃ (Path α β)
OrdinalPath = ∫ 𝒮ᴰ-Ord .UARel.ua
```

上面的泛等原理使用 `Path` 表述的, 也可以转换成归纳类型族 `_≡_` 表述.

```
OrdinalUnivalence : (α β : Ord ℓ) → (α ≃ₒ β) ≃ (α ≡ β)
OrdinalUnivalence α β = transport (α ≃ₒ β ≃_) Path≡Eq (OrdinalPath α β)
```

有了序数的泛等原理之后, 就可以通过找到两个序数间保持 `_<_` 关系的同伦等价来证明它们相等. 这体现了泛等基础的好处, 我们不需要商掉某个等价关系, 或者像质料集合论那样用超限归纳证明两个同构的序数外延相等.
