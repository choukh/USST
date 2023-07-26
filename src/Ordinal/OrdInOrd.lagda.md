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

前段是序数 `α` 的底集 `⟨ α ⟩` 里小于某个元素 `a` 的那些元素的类型 `B = Σ ⟨ α ⟩ (_≺ a)`, 它也构成了一个序数, 记作 `α ↓ a`.

```agda
infix 21 _↓_
_↓_ : (α : Ord 𝓊) → ⟨ α ⟩ → Ord 𝓊
α ↓ a = B , strB
  where
  open OrdStr (str α)
  B : Type _
  B = Σ ⟨ α ⟩ (_≺ a)
```

为了完成构造, 我们还需要说明 `B` 具有序数结构 `strB`. 首先取原序数的底序作为新序数的底序 `≺′`.

```agda
  _≺′_ : B → B → Type _
  (x , _) ≺′ (y , _) = x ≺ y
```

现在还需要说明 `≺′` 也是良序, 即满足命题性, 传递性, 外延性和良基性. 其中命题性和传递性是显然的.

```agda
  strB : OrdStr B
  strB = mkOrdStr _≺′_ $ mkWellOrdered
    {- 命题性 -} (λ _ _ → ≺-prop _ _)
    {- 传递性 -} (λ _ _ _ x<y y<z → ≺-trans _ _ _ x<y y<z)
```

(TODO)

```agda
    {- 外延性 -} (λ (x , x≺a) (y , y≺a) ext → Σ≡Prop
      (λ _ → ≺-prop _ _)
      (≺-ext x y λ z → (λ z≺x → ext (z , ≺-trans z x a z≺x x≺a) .fst z≺x)
                      , (λ z≺y → ext (z , ≺-trans z y a z≺y y≺a) .snd z≺y)))
```

(TODO)

```agda
    {- 良基性 -} (uncurry $ elim λ x IH x≺a → acc λ { (y , y≺a) y≺x → IH y y≺x y≺a })
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
↓-inj : {a b : ⟨ α ⟩} → α ↓ a ≡ α ↓ b → a ≡ b
↓-inj {α} {a} {b} eq = ≺-ext a b λ z →
  (↓-reflects-≼ a b (subst (λ - → (α ↓ a) ≤ -) eq       ≤-refl) z) ,
  (↓-reflects-≼ b a (subst (λ - → (α ↓ b) ≤ -) (sym eq) ≤-refl) z)
  where open OrdStr (str α)
```

(TODO)

```agda
↓≃ₒ↓ : ((f , _) : α ≤ β) (a : ⟨ α ⟩) → α ↓ a ≃ₒ β ↓ (f a)
↓≃ₒ↓ {α} {β} (f , emb) a = isoToEquiv i , mkIsOrderEquiv λ x y → isoToEquiv (j x y)
  where
  open OrdStr
  open IsOrdEmbed emb
  i : Iso ⟨ α ↓ a ⟩ ⟨ β ↓ f a ⟩
  Iso.fun       i (x , x≺a) = f x , pres≺ x a x≺a
  Iso.inv       i (y , y≺fa) = let (x , x≺a , _) = formsInitSeg y a y≺fa in x , x≺a
  Iso.leftInv   i (x , x≺a) = let (_ , _ , fw≡fx) = formsInitSeg (f x) a (pres≺ _ _ x≺a) in
    Σ≡Prop (λ _ → ≺-prop (str α) _ _) (inj fw≡fx)
  Iso.rightInv  i (y , y≺fa) = let (_ , _ , fx≡y) = formsInitSeg y a y≺fa in
    Σ≡Prop (λ _ → ≺-prop (str β) _ _) fx≡y

  module _ (u@(x , x≺a) v@(y , y≺fa) : ⟨ α ↓ a ⟩) where
    j : Iso (u ≺⟨ α ↓ a ⟩ v) (Iso.fun i u ≺⟨ β ↓ f a ⟩ Iso.fun i v)
    Iso.fun       j = pres≺ x y
    Iso.inv       j H =
      let (w , w≺y , fw≡fx) = formsInitSeg (f x) y H in
      subst (λ - → - ≺⟨ α ⟩ y) (inj fw≡fx) w≺y
    Iso.leftInv   j _ = ≺-prop (str α) _ _ _ _
    Iso.rightInv  j _ = ≺-prop (str β) _ _ _ _
```

(TODO)

```agda
↓≡↓ : ((f , _) : α ≤ β) {a : ⟨ α ⟩} → α ↓ a ≡ β ↓ (f a)
↓≡↓ f {a} = ≃ₒ→≡ $ ↓≃ₒ↓ f a
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
↓-reflects-≺ : (a b : ⟨ α ⟩) → α ↓ a < α ↓ b → a ≺⟨ α ⟩ b
↓-reflects-≺ {α} a b ↓<↓ = subst (λ a → a ≺⟨ α ⟩ b) (sym eq) bounded
  where
  bnd : ⟨ α ↓ b ⟩
  bnd = ↓<↓ .fst
  bounded : ↑ bnd ≺⟨ α ⟩ b
  bounded = ↑-bounded bnd
  eq : a ≡ ↑ bnd
  eq = ↓-inj $ (sym $ ↓<↓ .snd) ∙ ↓≡↓ ↓≤

↓-preserves-≺ : (a b : ⟨ α ⟩) → a ≺⟨ α ⟩ b → α ↓ a < α ↓ b
↓-preserves-≺ a b a≺b = (a , a≺b) , ↓≡↓ ↓≤
```

### 性质

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
    (↓-inj $ eq₁ ∙ sym eq₂)
```

(TODO)

```agda
  <-trans : Transitive
  <-trans α β γ (b , β↓b≡α) β<γ = subst (_< γ) β↓b≡α β↓b<γ
    where
    β↓b<γ : (β ↓ b) < γ
    β↓b<γ = <→≤ β<γ .fst b , sym (↓≡↓ $ <→≤ β<γ)
```

(TODO)

```agda
  <-ext : Extensional
  <-ext α β H = ≃ₒ→≡ $ isoToEquiv i , mkIsOrderEquiv λ x y → isoToEquiv (j x y)
    where
    f : ∀ a → α ↓ a < β
    f a = H _ .fst (a , refl)
    g : ∀ b → β ↓ b < α
    g b = H _ .snd (b , refl)
    i : Iso ⟨ α ⟩ ⟨ β ⟩
    Iso.fun       i = fst ∘ f
    Iso.inv       i = fst ∘ g
    Iso.leftInv   i a = ↓-inj $ g _ .snd ∙ f a .snd
    Iso.rightInv  i b = ↓-inj $ f _ .snd ∙ g b .snd
    module _ x y where
      j : Iso (x ≺⟨ α ⟩ y) (Iso.fun i x ≺⟨ β ⟩ Iso.fun i y)
      Iso.fun       j H = ↓-reflects-≺ _ _ $ subst2 _<_ (sym $ f x .snd) (sym $ f y .snd) (↓-preserves-≺ _ _ H)
      Iso.inv       j H = ↓-reflects-≺ _ _ $ subst2 _<_ (f x .snd)       (f y .snd)       (↓-preserves-≺ _ _ H)
      Iso.leftInv   j _ = OrdStr.≺-prop (str α) _ _ _ _
      Iso.rightInv  j _ = OrdStr.≺-prop (str β) _ _ _ _
```

(TODO)

```agda
  <-wf : WellFounded
  <-wf α = acc λ β (a , α↓a≡β) → subst Acc α↓a≡β (Acc↓ a)
    where
    open OrdStr (str α)
    Acc↓ : (a : ⟨ α ⟩) → Acc (α ↓ a)
    Acc↓ = elim λ a IH → acc λ β ((b , b≺a) , α↓a↓b≡β) →
      subst Acc (sym (↓≡↓ ↓≤) ∙ α↓a↓b≡β) (IH b b≺a)
```

(TODO)

```agda
  <-irrefl : Irreflexive
  <-irrefl = WellFounded→Irreflexive <-wf
```

(TODO)

```agda
  <-wo : WellOrdered
  <-wo = mkWellOrdered <-prop <-trans <-ext <-wf
```

## 吃自己

(TODO)

```agda
Ω : ∀ 𝓊 → Ord (𝓊 ⁺)
Ω 𝓊 = Ord 𝓊 , mkOrdStr _<_ <-wo
```

(TODO)

```agda
_ : ⟨ Ω 𝓊 ⟩ ≡ Ord 𝓊
_ = refl
```

(TODO)

```agda
ordInOrd : ∀ α → α ≃ₒ Ω 𝓊 ↓ α
ordInOrd {𝓊} α = isoToEquiv i , mkIsOrderEquiv λ x y → isoToEquiv (j x y)
  where
  open OrdStr
  i : Iso ⟨ α ⟩ ⟨ Ω 𝓊 ↓ α ⟩
  Iso.fun i x = α ↓ x , x , refl
  Iso.inv i (β , a , α↓a≡β) = a
  Iso.leftInv i _ = refl
  Iso.rightInv i (β , a , α↓a≡β) = ΣPathP $ α↓a≡β , isProp→PathP (λ _ → ≺-prop (str $ Ω 𝓊) _ _) _ _
  module _ x y where
    j : Iso (x ≺⟨ α ⟩ y) (Iso.fun i x ≺⟨ Ω 𝓊 ↓ α ⟩ Iso.fun i y)
    Iso.fun       j = ↓-preserves-≺ _ _
    Iso.inv       j = ↓-reflects-≺ _ _
    Iso.leftInv   j _ = ≺-prop (str α) _ _ _ _
    Iso.rightInv  j _ = ≺-prop (str $ Ω 𝓊 ↓ α) (Iso.fun i x) (Iso.fun i y) _ _
```

## 布拉利-福尔蒂悖论

(TODO)

```agda
Burali-Forti : ¬ (Σ α ∶ Ord 𝓊 , α ≃ₒ Ω 𝓊)
Burali-Forti {𝓊} (α , f) = <-irrefl _ H
  where
  g : Ω 𝓊 ↓ α ≃ₒ Ω 𝓊
  g = ≃ₒ-trans (≃ₒ-sym $ ordInOrd α) f
  H : Ω 𝓊 < Ω 𝓊
  H = α , ≃ₒ→≡ g
```
