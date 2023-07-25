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

为了完成构造, 我们还需要说明 `B` 具有序数结构 `strB`. 首先取原序数的底序作为新序数的底序 `≺′`.

```agda
    _≺′_ : B → B → Type 𝓊
    (x , _) ≺′ (y , _) = x ≺ y
```

现在还需要说明 `<` 也是良序. 其中命题性和传递性是显然的.

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
↓-reflects-≼ {α} a b le@(f , f-ordEmb) z z≺a =
  subst (λ - → - ≺⟨ α ⟩ b) ↑fz≡z (↑-bounded (f $ z , z≺a))
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

(TODO)

```agda
↓≃ₒ↓ : ((f , _) : α ≤ β) (a : ⟨ α ⟩) → α ↓ a ≃ₒ β ↓ (f a)
↓≃ₒ↓ {α} {β} (f , emb) a = isoToEquiv i , mkIsOrderEquiv ordEquiv
  where
  open OrdStr
  open IsOrdEmbed emb
  i : Iso ⟨ α ↓ a ⟩ ⟨ β ↓ f a ⟩
  Iso.fun       i (x , x≺a) = f x , pres≺ x a x≺a
  Iso.inv       i (y , y≺fa) = let (x , x≺a , _) = formsInitSeg y a y≺fa in x , x≺a
  Iso.leftInv  i (x , x≺a) = let (_ , _ , fw≡fx) = formsInitSeg (f x) a (pres≺ _ _ x≺a) in
    Σ≡Prop (λ _ → ≺-prop (str α) _ _) (inj fw≡fx)
  Iso.rightInv   i (y , y≺fa) = let (_ , _ , fx≡y) = formsInitSeg y a y≺fa in
    Σ≡Prop (λ _ → ≺-prop (str β) _ _) fx≡y
  ordEquiv : ∀ x y → x ≺⟨ α ↓ a ⟩ y ≃ (Iso.fun i x) ≺⟨ β ↓ f a ⟩ (Iso.fun i y)
  ordEquiv (x , x≺a) (y , y≺fa) = pres≺ x y , isEquivPres≺ where
    isEquivPres≺ : isEquiv (pres≺ x y)
    isEquivPres≺ = record { equiv-proof = λ fx≺fy →
      let (w , w≺y , fw≡fx) = formsInitSeg (f x) y fx≺fy
          x≺y : x ≺⟨ α ⟩ y
          x≺y = subst (λ - → - ≺⟨ α ⟩ y) (inj fw≡fx) w≺y
      in (x≺y , ≺-prop (str β) _ _ _ _) , λ _ → Σ≡Prop
          (λ _ → isProp→isSet (≺-prop (str β) _ _) _ _)
          (≺-prop (str α) _ _ _ _)
      }
```

(TODO)

```agda
↓≡↓ : ((f , _) : α ≤ β) (a : ⟨ α ⟩) → α ↓ a ≡ β ↓ (f a)
↓≡↓ f a = ≃ₒ→≡ $ ↓≃ₒ↓ f a
```

## 严格序

(TODO)

```agda
_<_ : Ord 𝓊 → Ord 𝓊 → Type (𝓊 ⁺)
α < β = Σ b ∶ ⟨ β ⟩ , β ↓ b ≡ α
```

```agda
<→≤ : α < β → α ≤ β
<→≤ {β} (b , β↓b≡α) = subst (_≤ β) β↓b≡α ↓≤
```

(TODO)

```agda
module _ {𝓊} where
  open BinaryRelation (_<_ {𝓊})
```

(TODO)

```agda
  <-prop : Propositional
  <-prop _ _ (b₁ , eq₁) (b₂ , eq₂) = Σ≡Prop
    (λ _ → isSetOrd _ _)
    (↓-inj b₁ b₂ $ eq₁ ∙ sym eq₂)
```

(TODO)

```agda
  <-trans : Transitive
  <-trans α β γ (b , β↓b≡α) β<γ = subst (_< γ) β↓b≡α β↓b<γ
    where
    β↓b<γ : (β ↓ b) < γ
    β↓b<γ = <→≤ β<γ .fst b , sym (↓≡↓ (<→≤ β<γ) b)
```

(TODO)

```agda
  <-ext : Extensional
  <-ext α β H = {!   !}
```

(TODO)

```agda
  <-wf : WellFounded
  <-wf α = acc λ β (a , α↓a≡β) → subst Acc α↓a≡β (Acc↓ a)
    where
    open OrdStr (str α)
    Acc↓ : (a : ⟨ α ⟩) → Acc (α ↓ a)
    Acc↓ = elim λ a IH → acc λ β ((b , b≺a) , α↓a↓b≡β) →
      subst Acc (sym (↓≡↓ ↓≤ _) ∙ α↓a↓b≡β) (IH b b≺a)
```

(TODO)

```agda
  <-wo : WellOrdered
  <-wo = mkWellOrdered <-prop <-trans <-ext <-wf
```

## 吃自己

(TODO)

```agda
Ord⁺ : ∀ 𝓊 → Ord (𝓊 ⁺)
Ord⁺ 𝓊 = Ord 𝓊 , mkOrdinalStr _<_ <-wo
```

## 布拉利-福尔蒂悖论的解决

(TODO)

```agda
Burali-Forti : ¬ (Σ α ∶ Ord 𝓊 , α ≃ₒ Ord⁺ 𝓊)
Burali-Forti = {!   !}
```
