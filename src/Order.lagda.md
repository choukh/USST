---
title: 泛等结构集合论 (3) 序结构
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
---

# 泛等结构集合论 (3) 序结构

> 交流Q群: 893531731  
> 本文源码: [Order.lagda.md](https://github.com/choukh/USST/blob/main/src/Order.lagda.md)  
> 高亮渲染: [Order.html](https://choukh.github.io/USST/Order.html)  

本章是关于序结构的一些抽象废话, 不过这对熟悉泛等基础中的工作方式是有帮助的.

```agda
{-# OPTIONS --cubical --safe #-}
module Order where
open import Preliminary
```

### 命题关系

给定类型 `A : Type ℓ` 及其上的关系 `R : A → A → Type ℓ′`

```agda
module _ {A : Type ℓ} (R : A → A → Type ℓ′) where
```

我们说 `R` 是一个 **命题 (propositional)** 关系, 当且仅当对任意 `x y : A`, `R x y` 是一个命题.

```agda
  Propositional : Type _
  Propositional = ∀ x y → isProp (R x y)
```

命题性本身是一个命题.

```agda
  isPropPropositional : isProp Propositional
  isPropPropositional = isPropΠ2 λ _ _ → isPropIsProp
```

## 序结构

(TODO: 介绍底集)

```agda
record IsOrder {A : Type ℓ} (_≤_ : A → A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  constructor mkIsOrder
  field
    order-prop : Propositional _≤_

unquoteDecl IsOrderIsoΣ = declareRecordIsoΣ IsOrderIsoΣ (quote IsOrder)

isPropIsOrder : {A : Type ℓ} {_≤_ : A → A → Type ℓ′} → isProp (IsOrder _≤_)
isPropIsOrder = isOfHLevelRetractFromIso 1 IsOrderIsoΣ $ isPropPropositional _

record OrderStr (ℓ′ : Level) (A : Type ℓ) : Type (ℓ ⊔ ℓ-suc ℓ′) where
  constructor mkOrderStr
  field
    _≤_ : A → A → Type ℓ′
    isOrder : IsOrder _≤_

Order : ∀ ℓ ℓ′ → Type _
Order ℓ ℓ′ = TypeWithStr ℓ (OrderStr ℓ′)

private variable
  M N : Order ℓ ℓ′
```

## 序等价

```agda
record IsOrderEquiv {A : Type ℓ₁} {B : Type ℓ₂}
  (M : OrderStr ℓ₁′ A) (e : A ≃ B) (N : OrderStr ℓ₂′ B) : Type (ℓ₁ ⊔ ℓ₁′ ⊔ ℓ₂′) where
  constructor mkIsOrderEquiv
  private
    module ₁ = OrderStr M
    module ₂ = OrderStr N
    f = equivFun e
  field
    pres≤ : (x y : A) → x ₁.≤ y ≃ f x ₂.≤ f y

OrderEquiv : Order ℓ₁ ℓ₁′ → Order ℓ₂ ℓ₂′ → Type _
OrderEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsOrderEquiv (str M) e (str N)
```

## 序结构的泛等原理

(TODO: 介绍SIP)

```agda
𝒮ᴰ-Order : DUARel (𝒮-Univ ℓ) (OrderStr ℓ′) (ℓ ⊔ ℓ′)
𝒮ᴰ-Order = 𝒮ᴰ-Record (𝒮-Univ _) IsOrderEquiv
  (fields:
    data[ _≤_ ∣ autoDUARel _ _ ∣ pres≤ ]
    prop[ isOrder ∣ (λ _ _ → isPropIsOrder) ])
  where
  open OrderStr
  open IsOrderEquiv
```

两个序结构的等价等价于它们的相等.

```agda
OrderPath : (M N : Order ℓ₁ ℓ₂) → OrderEquiv M N ≃ (Path M N)
OrderPath = ∫ 𝒮ᴰ-Order .UARel.ua
```
