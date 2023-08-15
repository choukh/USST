---
title: 泛等结构集合论 (4) 序数的定义及其泛等原理
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
zhihu-url: https://zhuanlan.zhihu.com/p/643453391
---

# 泛等结构集合论 (4) 序数的定义及其泛等原理

> 交流Q群: 893531731  
> 本文源码: [Ordinal.Base.lagda.md](https://github.com/choukh/USST/blob/main/src/Ordinal/Base.lagda.md)  
> 高亮渲染: [Ordinal.Base.html](https://choukh.github.io/USST/Ordinal.Base.html)  

本章将复刻质料集合论的重要概念: 序数.

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --hidden-argument-puns #-}

module Ordinal.Base where
open import Preliminary
```

## 序关系的一些性质

说白了, 一个序数就是由一个集合以及该集合上的一个满足一定性质的序关系所组成的结构. 我们先定义这个序关系需要满足的性质.

给定类型 `A : Type 𝓊` 及其上的序关系 `_≺_ : A → A → Type 𝓋`

```agda
module BinaryRelation {A : Type 𝓊} (_≺_ : A → A → Type 𝓋) where
```

### 命题性

我们说 `_≺_` 是一个 **命题 (propositional)** 关系, 当且仅当对任意 `x y : A`, `x ≺ y` 是一个命题.

```agda
  Propositional : Type _
  Propositional = ∀ x y → isProp (x ≺ y)
```

命题性本身是一个命题.

```agda
  isPropPropositional : isProp Propositional
  isPropPropositional = isPropΠ2 λ _ _ → isPropIsProp
```

### 反自反性

我们说 `_≺_` 是一个 **反自反 (irreflexive)** 关系, 当且仅当对任意 `x : A`, `x ⊀ x`.

```agda
  _⊀_ : A → A → Type 𝓋
  x ⊀ y = ¬ x ≺ y

  Irreflexive : Type _
  Irreflexive = ∀ x → x ⊀ x
```

反自反性是一个命题.

```agda
  isPropIrreflexive : isProp Irreflexive
  isPropIrreflexive = isPropΠ2 λ _ _ → isProp⊥
```

### 传递性

我们说 `_≺_` 是一个 **传递 (transitive)** 关系, 当且仅当对任意 `x y z : A`, `x ≺ y` 与 `y ≺ z` 蕴含 `x ≺ z`.

```agda
  Transitive : Type _
  Transitive = ∀ x y z → x ≺ y → y ≺ z → x ≺ z
```

如果`_≺_` 是一个命题关系, 那么传递性是一个命题.

```agda
  isPropTransitive : Propositional → isProp Transitive
  isPropTransitive prop = isPropΠ5 λ _ _ _ _ _ → prop _ _
```

### 外延性

我们说 `_≺_` 是一个 **外延 (extensional)** 关系, 当且仅当对任意 `x y : A`, 如果对任意 `z : A` 都有 `z ≺ x` 当且仅当 `z ≺ y`, 那么 `x ≡ y`.

```agda
  Extensional : Type _
  Extensional = ∀ x y → (∀ z → z ≺ x ↔ z ≺ y) → x ≡ y
```

如果 `A` 是集合, 那么外延性是命题.

```agda
  isPropExtensional : isSet A → isProp Extensional
  isPropExtensional A-set = isPropΠ3 λ _ _ _ → A-set _ _
```

**引理** 如果 `_≺_` 同时具有命题性和外延性那么 `A` 是集合.  
**证明梗概** 由引理 `Collapsible≡→isSet`, 只要证明 `A` 上的相等类型 `x ≡ y` 可折叠, 就证明了 `A` 是集合. 可折叠是说能构造 `x ≡ y` 的自映射 `f` 且 `f` 是一个 2-常函数 (`∀ x y → f x ≡ f y`). 只要用作为自变量的那个 `eq : x ≡ y` 替换外延性的前提 `z ≺ x ↔ z ≺ y` 就能得到另一个 `x ≡ y`. 由于 `_≺_` 是命题, 所以 `z ≺ x ↔ z ≺ y` 是命题, 所以 `f` 是 2-常函数. ∎

```agda
  open import Cubical.Foundations.Function using (2-Constant)
  open import Cubical.Relation.Nullary using (Collapsible; Collapsible≡→isSet)

  Extensional→isSet : Propositional → Extensional → isSet A
  Extensional→isSet prop ext = Collapsible≡→isSet λ x y → collapser x y , didCollapse x y
    where
    collapser : ∀ x y → x ≡ y → x ≡ y
    collapser x y eq = ext x y λ z → →: (subst (z ≺_) eq) ←: (subst (z ≺_) (sym eq))
    didCollapse : ∀ x y → 2-Constant (collapser x y)
    didCollapse x y p q = cong (ext x y) $ funExt λ _ → isProp↔ (prop _ _) (prop _ _) _ _
```

### 可及性

我们说在 `_≺_` 关系下, 一个 `x : A` **可及 (accessible)**, 当且仅当对任意 `y ≺ x`, `y` 也可及.

```agda
  data Acc (x : A) : Type (𝓊 ⊔ 𝓋) where
    acc : (∀ y → y ≺ x → Acc y) → Acc x
```

可及性是一个命题. 下面的证明中暴露了 cubical 的底层机制, 就是那个间点 `i`, 以使证明更简洁. 也可以不暴露, 只需证 `H₁` 等于 `H₂`, 它们都具有 `∀ y → y ≺ x → Acc y` 类型. 由归纳假设, `Acc y` 是命题, 所以这个Π类型也是命题, 所以它的两个项 `H₁` 与 `H₂` 相等.

```agda
  isPropAcc : ∀ x → isProp (Acc x)
  isPropAcc x (acc IH₁) (acc IH₂) i = acc λ y y≺x → isPropAcc y (IH₁ y y≺x) (IH₂ y y≺x) i
```

可及性的消去规则 `acc-elim` 可以看作是数学归纳法的更一般形式, 它说如果对任意 `x` 我们都能通过证明任意 `y ≺ x` 有 `P y` 来证明 `P x`, 那么任意可及的 `x` 都有 `P x`.

```agda
  acc-elim : {P : A → Type 𝓌} → (∀ x → (∀ y → y ≺ x → P y) → P x) → ∀ x → Acc x → P x
  acc-elim {P} H = aux where
    aux : ∀ x → Acc x → P x
    aux x (acc IH) = H x λ y y≺x → aux y (IH y y≺x)
```

有时我们还要用到双参数形式的消去规则.

```agda
  acc-elim2 : {R : A → A → Type 𝓌}
    → (∀ x y → (∀ u v → u ≺ x → v ≺ y → R u v) → R x y)
    → ∀ x y → Acc x → Acc y → R x y
  acc-elim2 {R} H = aux where
    aux : ∀ x y → Acc x → Acc y → R x y
    aux x y (acc IHx) (acc IHy) = H x y λ u v u≺x v≺y → aux u v (IHx u u≺x) (IHy v v≺y)
```

### 良基性

我们说 `_≺_` 是一个 **良基 (well-founded)** 关系, 当且仅当任意 `x : A` 都可及.

```agda
  WellFounded : Type _
  WellFounded = ∀ x → Acc x
```

良基性也是一个命题.

```agda
  isPropWellFounded : isProp WellFounded
  isPropWellFounded = isPropΠ λ _ → isPropAcc _
```

在 `acc-elim` 的基础上, 以良基性取代 `x` 的可及条件, 就得到了良基关系的消去规则 `wf-elim`.

```agda
  wf-elim : {P : A → Type 𝓌} → WellFounded → (∀ x → (∀ y → y ≺ x → P y) → P x) → ∀ x → P x
  wf-elim wf H x = acc-elim H x (wf x)

  wf-elim2 : {R : A → A → Type 𝓌} → WellFounded →
    (∀ x y → (∀ u v → u ≺ x → v ≺ y → R u v) → R x y) → ∀ x y → R x y
  wf-elim2 wf H x y = acc-elim2 H x y (wf x) (wf y)
```

注意这里说的 `P` 指任意以 `A` 为索引的类型 `A → Type 𝓌`. 把 `P` 看作谓词, `wf-elim` 可以看作是一种归纳法.

用常函数实例化 `P` , `wf-elim` 则可以看作是一种递归原理.

```agda
  wf-rec : {B : Type 𝓌} → WellFounded → (∀ x → (∀ y → y ≺ x → B) → B) → A → B
  wf-rec = wf-elim
```

由良基消去可以立即证明良基性蕴含反自反性.

```agda
  WellFounded→Irreflexive : WellFounded → Irreflexive
  WellFounded→Irreflexive wf = wf-elim wf λ x IH x≺x → IH x x≺x x≺x
```

### 良序性

我们说 `_≺_` 是一个 **良序 (well-ordered)** 关系, 当且仅当: `_≺_` 有命题性, 传递性, 外延性和良基性.

```agda
  record WellOrdered : Type (𝓊 ⊔ 𝓋) where
    constructor mkWellOrdered
    field
      ≺-prop    : Propositional
      ≺-trans   : Transitive
      ≺-ext     : Extensional
      ≺-wf      : WellFounded
```

良序关系是反自反的, 且其底层类型必是集合, 我们今后称之为**底集 (underlying set)**. 经典数学里面一般是把这里的外延性换成了三歧性, 但在直觉主义中外延性更容易处理. 此外, HoTT Book 也有相应的定义, 见 Def 10.3.17, 它要求 "`A` 是集合", 但这不是必须的, Escardó 首先证明了[这一点](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Ordinals.Notions.html#8277)

```agda
    ≺-irrefl : Irreflexive
    ≺-irrefl = WellFounded→Irreflexive ≺-wf

    underlying-set : isSet A
    underlying-set = Extensional→isSet ≺-prop ≺-ext
```

由于良序性里面的每个条件都是命题, 所以良序性也是一个命题.

```agda
  isPropWellOrdered : isProp WellOrdered
  isPropWellOrdered = isOfHLevelRetractFromIso 1 WellOrderedIsoΣ $ aux
    where
    unquoteDecl WellOrderedIsoΣ = declareRecordIsoΣ WellOrderedIsoΣ (quote WellOrdered)
    aux : ∀ x y → x ≡ y
    aux x _ = ΣPathP (isPropPropositional _ _
            , ΣPathP (isPropTransitive ≺-prop _ _
            , ΣPathP (isPropExtensional underlying-set _ _
            , isPropWellFounded _ _)))
      where open WellOrdered (Iso.inv WellOrderedIsoΣ x)
```

## 序数的定义

为了方便 `𝒮ᴰ-Record` 宏处理, 我们遵循 cubical 库的做法, 先用 record 类型定义序数结构, 然后用Σ类型把序数定义为类型宇宙配备上序数结构.

### 序数结构

一个类型 `A` 配备上一个良序 `_≺_` 就构成了一个序数结构 `OrdStr`. 注意我们这里让 `_≺_` 与底集 `A` 居留于同一宇宙, 这可以让形式更简单, 反正 `_≺_` 是命题, 而我们有 `PR` 可以随时降级命题宇宙.

```agda
record OrdStr (A : Type 𝓊) : Type (𝓊 ⁺) where
  constructor mkOrdStr
  open BinaryRelation
  field
    _≺_ : A → A → Type 𝓊
    ≺-wo : WellOrdered _≺_
  open WellOrdered ≺-wo public
```

我们有序数底层结构的良基消去及其计算规则.

```agda
  elim : {P : A → Type 𝓌} → (∀ x → (∀ y → y ≺ x → P y) → P x) → ∀ x → P x
  elim = wf-elim _≺_ ≺-wf

  elim2 : {R : A → A → Type 𝓌} → (∀ x y → (∀ u v → u ≺ x → v ≺ y → R u v) → R x y) → ∀ x y → R x y
  elim2 = wf-elim2 _≺_ ≺-wf

  rec : {B : Type 𝓌} → (∀ x → (∀ y → y ≺ x → B) → B) → A → B
  rec = elim
```

### 序数宇宙

类型宇宙配备上序数结构就构成了序数宇宙 `Ord`. 注意 `Ord` 后面跟的 `𝓊` 指的是底集所在的宇宙, 而 `Ord` 本身位于 `𝓊 ⁺` 宇宙.

```agda
Ord : (𝓊 : Level) → Type (𝓊 ⁺)
Ord 𝓊 = TypeWithStr 𝓊 OrdStr
```

我们今后都用 α β γ 等符号表示序数.

```agda
variable α β γ δ : Ord 𝓊
```

### 底集

我们用 `⟨ α ⟩` 表示序数的底集, 可以证明它确实是一个集合.

```agda
ordSet : isSet ⟨ α ⟩
ordSet {α} = OrdStr.underlying-set (str α)
```

### 底序

当同时讨论多个序数中的 `≺` 关系时, 我们用 `x ≺⟨ α ⟩ y` 的记法标记 `≺` 所属的序数. 我们把 `≺⟨ α ⟩` 叫做 `α` 的底序, 与底集相对应, 它们共同组成了一个序数的底层结构. 若把 `≺` 看作"属于"关系, `∀ z → z ≺⟨ α ⟩ x → z ≺⟨ α ⟩ y` 则可以看作是"包含"关系, 记作 `≼`. 但要注意这些都只是类比的说法, `x` 和 `y` 本身不是集合.

以下代码定义了一个支持 `x ≺⟨ α ⟩ y` 和 `x ≼⟨ α ⟩ y` 记法的类型类 (typeclass) `Underlying`.

```agda
record Underlying {𝓊} (O : Type (𝓊 ⁺)) : Type (𝓊 ⁺) where
  field
    underlyingSet : O → Type 𝓊
    underlyingRel : (α : O) → underlyingSet α → underlyingSet α → Type 𝓊
  syntax underlyingRel α x y = x ≺⟨ α ⟩ y

  underlyingPoRel : (α : O) → underlyingSet α → underlyingSet α → Type 𝓊
  underlyingPoRel α x y = ∀ z → z ≺⟨ α ⟩ x → z ≺⟨ α ⟩ y
  syntax underlyingPoRel α x y = x ≼⟨ α ⟩ y

open Underlying ⦃...⦄ public
```

我们对序数实装 `Underlying` 类型类.

```agda
instance
  underlying : Underlying (Ord 𝓊)
  underlyingSet ⦃ underlying ⦄ = ⟨_⟩
  underlyingRel ⦃ underlying ⦄ = OrdStr._≺_ ∘ str
```

## 序数等价

我们说两个序数的底集间的同伦等价 `e : A ≃ B` 是一个序数等价, 当且仅当 `e` 保持序关系. 注意这里的"保持序关系"也必须用同伦等价来表达, 今后叫它序等价, 记作 `hPres≺`, 定义为对任意 `x y : A` 有 `x ≺₁ y` 与 `f x ≺₂ f y` 同伦等价, 其中 `≺₁` 和 `≺₂` 分别是 `A` 和 `B` 上的序关系, `f` 是 `A ≃ B` 的底层函数.

```agda
module _ {A : Type 𝓊} {B : Type 𝓊′} (a : OrdStr A) (f : A ≃ B) (b : OrdStr B) where

  record IsOrdEquiv : Type (𝓊 ⊔ 𝓊′) where
    constructor mkIsOrderEquiv
    open OrdStr a renaming (_≺_ to _≺₁_)
    open OrdStr b renaming (_≺_ to _≺₂_)
    field
      hPres≺ : (x y : A) → x ≺₁ y ≃ (f ⁺¹) x ≺₂ (f ⁺¹) y
```

由同伦等价的命题性, "是序数等价"也是一个命题. 这是很有用的性质, 会在下一章用到.

```agda
  isPropIsOrdEquiv : isProp IsOrdEquiv
  isPropIsOrdEquiv = isOfHLevelRetractFromIso 1 IsOrdEquivIsoΣ $ aux
    where
    unquoteDecl IsOrdEquivIsoΣ = declareRecordIsoΣ IsOrdEquivIsoΣ (quote IsOrdEquiv)
    aux : ∀ x y → x ≡ y
    aux = isPropΠ2 λ _ _ → isPropΣ (isProp→ $ ≺-prop _ _) (λ _ → isPropIsEquiv _)
      where open OrdStr b
```

序数间的同伦等价 `α ≃ₒ β` 定义为保持序关系的底集间同伦等价 `A ≃ B`.

```agda
_≃ₒ_ : Ord 𝓊 → Ord 𝓊′ → Type (𝓊 ⊔ 𝓊′)
α ≃ₒ β = Σ f ∶ ⟨ α ⟩ ≃ ⟨ β ⟩ , IsOrdEquiv (str α) f (str β)
```

可以证明序数等价确实是等价关系, 由同伦等价的自反性, 对称性和传递性即得.

```agda
≃ₒ-refl : α ≃ₒ α
≃ₒ-refl = idEquiv _ , mkIsOrderEquiv λ x y → idEquiv _

≃ₒ-sym : α ≃ₒ β → β ≃ₒ α
≃ₒ-sym {α} {β} (α≃β , eqv) = invEquiv α≃β ,
  mkIsOrderEquiv λ x y → invEquiv $
    subst2 (λ u v → _ ≺⟨ α ⟩ _ ≃ u ≺⟨ β ⟩ v)
      (secIsEq (snd α≃β) x) (secIsEq (snd α≃β) y)
      (hPres≺ (α≃β ⁻¹ $ x) (α≃β ⁻¹ $ y))
  where open IsOrdEquiv eqv

≃ₒ-trans : α ≃ₒ β → β ≃ₒ γ → α ≃ₒ γ
≃ₒ-trans (α≃β , eqv₁) (β≃γ , eqv₂) = compEquiv α≃β β≃γ ,
  mkIsOrderEquiv λ x y → compEquiv
    (hPres≺ eqv₁ x y) (hPres≺ eqv₂ (α≃β ⁺¹ $ x) (α≃β ⁺¹ $ y))
  where open IsOrdEquiv
```

序数等价推导链记号:

```agda
infixr 2 _≃ₒ⟨_⟩_ _≃ₒ˘⟨_⟩_ _≃ₒ⟨⟩_
infix  3 _≃ₒ∎

_≃ₒ⟨_⟩_ : (α : Ord 𝓊) {β : Ord 𝓋} {γ : Ord 𝓌} → α ≃ₒ β → β ≃ₒ γ → α ≃ₒ γ
_ ≃ₒ⟨ α≃ₒβ ⟩ β≃ₒγ = ≃ₒ-trans α≃ₒβ β≃ₒγ

_≃ₒ˘⟨_⟩_ : (α : Ord 𝓊) {β : Ord 𝓋} {γ : Ord 𝓌} → β ≃ₒ α → β ≃ₒ γ → α ≃ₒ γ
_ ≃ₒ˘⟨ β≃ₒα ⟩ β≃ₒγ = ≃ₒ-trans (≃ₒ-sym β≃ₒα) β≃ₒγ

_≃ₒ⟨⟩_ : (α : Ord 𝓊) {β : Ord 𝓋} → α ≃ₒ β → α ≃ₒ β
_ ≃ₒ⟨⟩ α≃ₒβ = α≃ₒβ

_≃ₒ∎ : (α : Ord 𝓊) → α ≃ₒ α
_ ≃ₒ∎ = ≃ₒ-refl
```

## 序数的泛等原理

我们使用宏 `𝒮ᴰ-Record` 得到序数的泛等原理. 不需要深究其语法, 只需认为它是一种 boilerplate (样板代码), 在 cubical 的代数模块里面也被大量使用. 简而言之, 这段代码说, 序数包括两个"字段", 一个是 `_≺_`, 它被同伦等价保持了, 再一个是 `≺-wo`, 它是个命题, 不影响结构. 这样就可以用 `𝒮ᴰ-Record` 拿到 `𝒮ᴰ-Ord : DUARel ...` 这一串东西.

```agda
𝒮ᴰ-Ord : DUARel (𝒮-Univ 𝓊) OrdStr 𝓊
𝒮ᴰ-Ord = 𝒮ᴰ-Record (𝒮-Univ _) IsOrdEquiv
  (fields:
    data[ _≺_ ∣ autoDUARel _ _ ∣ hPres≺ ]
    prop[ ≺-wo ∣ (λ _ _ → isPropWellOrdered _) ])
  where
  open OrdStr
  open IsOrdEquiv
  open BinaryRelation
```

然后就可以用 `∫` 从 `𝒮ᴰ-Ord` 中取出序数的泛等原理: 两个序数的等价等价于它们的相等.

```agda
OrdPath : (α β : Ord 𝓊) → (α ≃ₒ β) ≃ (α ≡ β)
OrdPath = ∫ 𝒮ᴰ-Ord .UARel.ua
```

有了序数的泛等原理之后, 就可以通过找到两个序数间保持 `_≺_` 关系的同伦等价来证明它们相等. 这体现了泛等基础的好处, 我们不需要商掉某个等价关系, 也不用像质料集合论那样用超限归纳证明两个同构的序数外延相等.

```agda
≃ₒ→≡ : α ≃ₒ β → α ≡ β
≃ₒ→≡ = OrdPath _ _ ⁺¹

≡→≃ₒ : α ≡ β → α ≃ₒ β
≡→≃ₒ = OrdPath _ _ ⁻¹
```
