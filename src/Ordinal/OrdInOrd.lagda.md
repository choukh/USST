---
title: 泛等结构集合论 (5) 吃自己:序数宇宙也是序数
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
---

# 泛等结构集合论 (5) 吃自己: 序数宇宙也是序数

> 交流Q群: 893531731  
> 本文源码: [Ordinal.OrdInOrd.lagda.md](https://github.com/choukh/USST/blob/main/src/Ordinal/OrdInOrd.lagda.md)  
> 高亮渲染: [Ordinal.OrdInOrd.html](https://choukh.github.io/USST/Ordinal.OrdInOrd.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification --hidden-argument-puns #-}
module Ordinal.OrdInOrd where
open import Preliminary
open import Ordinal.Base
open import Ordinal.Order
```

## 前段

上一章已经提到了前段, 它就是序数 `α` 的底集 `⟨ α ⟩` 里小于某个元素 `a` 的那些元素 `B = Σ ⟨ α ⟩ (_≺ a)`, 它们也构成了一个序数, 记作 `α ↓ a`.

```agda
module _ (α : Ord 𝓊) (a : ⟨ α ⟩) where
  open OrdStr (str α)

  infix 21 _↓_
  _↓_ : Ord 𝓊
  _↓_ = B , strB
    where
    B : Type 𝓊
    B = Σ ⟨ α ⟩ (_≺ a)
```

为了完成构造, 我们还需要提供 `B` 的序数结构 `strB`. 首先取原序数的底序作为新序数的底序 `≺′`.

```agda
    _≺′_ : B → B → Type 𝓊
    (x , _) ≺′ (y , _) = x ≺ y
```

现在还需要说明 `<` 也是良序. 命题性和传递性是显然的.

```agda
    strB : OrdStr B
    strB = mkOrdinalStr _≺′_ $ BinaryRelation.mkWellOrdered
      (λ _ _ → ≺-prop _ _)
      (λ _ _ _ x<y y<z → ≺-trans _ _ _ x<y y<z)
```

(TODO)

```agda
      (λ (x , x≺a) (y , y≺a) ext → Σ≡Prop
        (λ _ → ≺-prop _ _)
        (≺-ext x y λ z → (λ z≺x → ext (z , ≺-trans z x a z≺x x≺a) .fst z≺x)
                       , (λ z≺y → ext (z , ≺-trans z y a z≺y y≺a) .snd z≺y)))
```

(TODO)

```agda
      (uncurry $ elim λ x IH x≺a → acc λ { (y , y≺a) y≺x → IH y y≺x y≺a })
        where open BinaryRelation
```

### 前段嵌入

(TODO)

```agda
module _ {α : Ord 𝓊} {a : ⟨ α ⟩} where
  open OrdStr (str α)

  ↑ : ⟨ α ↓ a ⟩ → ⟨ α ⟩
  ↑ = fst
```

(TODO)

```agda
  ↑-bounded : (x : ⟨ α ↓ a ⟩) → ↑ x ≺⟨ α ⟩ a
  ↑-bounded = snd
```

前段嵌入是一个序数嵌入.

```agda
  ↑-ordEmbed : IsOrdEmbed ↑
  ↑-ordEmbed = mkIsOrdEmbed (λ _ _ → idfun _)
    λ { b (a′ , a′≺a) b≺a′ → (b , ≺-trans _ _ _ b≺a′ a′≺a) , b≺a′ , refl }
```

### 单射性

(TODO)

```agda
↓≤ : {a : ⟨ α ⟩} → α ↓ a ≤ α
↓≤ = ↑ , ↑-ordEmbed
```

(TODO)

```agda
↓-reflects-≼ : (a b : ⟨ α ⟩) → α ↓ a ≤ α ↓ b → a ≼⟨ α ⟩ b
↓-reflects-≼ {α} a b le@(f , f-ordEmb) z z≺a = subst (λ - → - ≺⟨ α ⟩ b) ↑fz≡z (↑-bounded (f $ z , z≺a))
  where
  ↑∘f≡↑ : ↑ ∘ f ≡ ↑
  ↑∘f≡↑ = ordEmbed-unique (↑ ∘ f) ↑ (≤-trans le ↓≤ .snd) ↑-ordEmbed
  ↑fz≡z : ↑ (f $ z , z≺a) ≡ z
  ↑fz≡z = funExt⁻ ↑∘f≡↑ (z , z≺a)
```

(TODO)

```agda
↓-inj : (a b : ⟨ α ⟩) → α ↓ a ≡ α ↓ b → a ≡ b
↓-inj {α} a b eq = ≺-ext a b λ z →
  (↓-reflects-≼ a b (subst (λ - → (α ↓ a) ≤ -) eq       ≤-refl) z) ,
  (↓-reflects-≼ b a (subst (λ - → (α ↓ b) ≤ -) (sym eq) ≤-refl) z)
  where open OrdStr (str α)
```

## 严格序

(TODO)

```agda
_<_ : Ord 𝓊 → Ord 𝓋 → Type (𝓊 ⊔ 𝓋)
α < β = Σ b ∶ ⟨ β ⟩ , α ≃ₒ (β ↓ b)
```

(TODO)

```agda
<-prop : (α : Ord 𝓊) (β : Ord 𝓋) → isProp (α < β)
<-prop α β (b₁ , eqv₁) (b₂ , eqv₂) = Σ≡Prop
  (λ _ → isPropOrdEquiv _ _)
  {!   !}
  --(↓-inj b₁ b₂ ({!   !} ∙ (OrdPath _ _ ⁺¹) {!   !}))
```
