---
title: 泛等结构集合论 (7) 直觉主义阿列夫层级
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
---

# 泛等结构集合论 (7) 直觉主义阿列夫层级

> 交流Q群: 893531731  
> 本文源码: [Cardinal.Base.lagda.md](https://github.com/choukh/USST/blob/main/src/Cardinal/Base.lagda.md)  
> 高亮渲染: [Cardinal.Base.html](https://choukh.github.io/USST/Cardinal.Base.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification --hidden-argument-puns #-}

module Cardinal.Base where
```

## 前言

我们在之前几讲介绍了泛等基础对序数的处理. 简而言之, 因为泛等基础中同构的良序结构是相等的, 所以我们直接把良序结构视作序数.

本讲我们介绍泛等基础如何处理集合论中的另一个重要概念: 基数. 简单来说, 每个集合 `a : hSet 𝓊` 本身几乎可以视作它自己的基数. 因为同构 (也就是能建立双射) 的集合在泛等基础中是相等的. 这正是 `hSet` 上的泛等原理所说的:

`(a ≃ b) ≃ (a ≡ b)`

或者换成更传统的符号, 我们有

$$(a ↔ b) ↔ (a = b)$$

传统上我们用的是加上了取基数符号的版本:

$$(a ↔ b) ↔ (∣ a ∣ = ∣ b ∣)$$

只不过我们这里不需要取了. 这就是为什么说每个集合本身几乎可以视作它自己的基数.

这里说"几乎"是因为, 我们希望基数的相等 `∣ a ∣ ≡ ∣ b ∣` 是一个命题, 但集合本身的相等 `a ≡ b` 不是命题, 因为集合宇宙本身不是集合, 而是一个群胚.

使得基数的相等是命题就是泛等基础中对集合 `a` 取 `∣ a ∣` 的唯一目的.

可能有点出乎意料地, 集合截断的构造子 `∣_∣₂` 就是我们需要的 `∣_∣`, 具体原因会在后面解释, 这里直接先对它做重命名处理.

```agda
open import Preliminary renaming (∣_∣₂ to ∣_∣)
```

```agda
open import Ordinal hiding (≤-refl; ≤-trans)
  renaming ( _≤_ to _≤ₒ_; ≤-prop to ≤ₒ-prop
           ; _<_ to _<ₒ_; <-prop to <ₒ-prop)
open BinaryRelation
```

## 基数

```agda
Card : (𝓊 : Level) → Type (𝓊 ⁺)
Card 𝓊 = ∥ hSet 𝓊 ∥₂
```

```agda
isSetCard : isSet (Card 𝓊)
isSetCard = squash₂
```

```agda
cardRec : (hSet 𝓊 → hProp (𝓊 ⁺)) → Card 𝓊 → hProp (𝓊 ⁺)
cardRec P = ∥∥₂-rec {B = hProp _} isSetHProp P
```

```agda
cardEqIso∥Eq∥ : {a b : hSet 𝓊} → Iso (∣ a ∣ ≡ ∣ b ∣) ∥ a ≡ b ∥₁
Iso.fun (cardEqIso∥Eq∥ {𝓊} {b}) p = subst (λ κ → cardRec (λ a → ∥ a ≡ b ∥ₚ) κ .fst) (sym p) ∣ refl ∣₁
Iso.inv       cardEqIso∥Eq∥ = ∥∥₁-rec (isSetCard _ _) (cong ∣_∣)
Iso.rightInv  cardEqIso∥Eq∥ _ = squash₁ _ _
Iso.leftInv   cardEqIso∥Eq∥ _ = isSetCard _ _ _ _
```

```agda
equivToCardEq : {a b : hSet 𝓊} → ⟨ a ⟩ ≃ ⟨ b ⟩ → ∣ a ∣ ≡ ∣ b ∣
equivToCardEq eqv = cong ∣_∣ $ Σ≡Prop (λ _ → isPropΠ2 λ _ _ → isPropIsProp) (ua eqv)
```

```agda
cardEqToEquip : {a b : hSet 𝓊} → ∣ a ∣ ≡ ∣ b ∣ → ⟨ a ⟩ ≈ ⟨ b ⟩
cardEqToEquip eq = ∥∥₁-map (λ x → subst (λ - → _ ≃ ⟨ - ⟩) x (idEquiv _)) (Iso.fun cardEqIso∥Eq∥ eq)
```

```agda
cardEqIsoEquip : {a b : hSet 𝓊} → Iso (∣ a ∣ ≡ ∣ b ∣) (⟨ a ⟩ ≈ ⟨ b ⟩)
Iso.fun       cardEqIsoEquip = cardEqToEquip
Iso.inv       cardEqIsoEquip = ∥∥₁-rec (isSetCard _ _) equivToCardEq
Iso.rightInv  cardEqIsoEquip _ = squash₁ _ _
Iso.leftInv   cardEqIsoEquip _ = isSetCard _ _ _ _
```

```agda
cardEq≃Equip : {a b : hSet 𝓊} → (∣ a ∣ ≡ ∣ b ∣) ≃ (⟨ a ⟩ ≈ ⟨ b ⟩)
cardEq≃Equip = isoToEquiv cardEqIsoEquip
```

## 基数的序

```agda
_≤ₕ_ : Card 𝓊 → Card 𝓋 → hProp (𝓊 ⊔ 𝓋)
_≤ₕ_ = ∥∥₂-rec2 isSetHProp λ (A , _) (B , _) → A ≲ B , squash₁
```

```agda
_≤_ : Card 𝓊 → Card 𝓋 → Type (𝓊 ⊔ 𝓋)
κ ≤ μ = ⟨ κ ≤ₕ μ ⟩

≤-prop : (κ : Card 𝓊) (μ : Card 𝓋) → isProp (κ ≤ μ)
≤-prop κ μ = str (κ ≤ₕ μ)

≤-set : (κ : Card 𝓊) (μ : Card 𝓋) → isSet (κ ≤ μ)
≤-set κ μ = isProp→isSet (≤-prop κ μ)
```

```agda
≤-refl : (κ : Card 𝓊) → κ ≤ κ
≤-refl = ∥∥₂-elim (λ _ → ≤-set _ _) λ _ → ∣ ↪-refl ∣₁
```

```agda
≤-trans : (κ : Card 𝓊) (μ : Card 𝓋) (ν : Card 𝓌) → κ ≤ μ → μ ≤ ν → κ ≤ ν
≤-trans = ∥∥₂-elim (λ _ → isSetΠ2 λ _ _ → isSet→ $ isSet→ $ ≤-set _ _)
  λ _ → ∥∥₂-elim2 (λ _ _ → isSet→ $ isSet→ $ ≤-set _ _) λ _ _ → ∥∥₁-map2 ↪-trans
```

## 哈特格斯数

```agda
module Hartogs (A : Type 𝓊) (Aset : isSet A) where

  ℌ : Ord (𝓊 ⁺)
  ℌ = tieup h
    where
    h : EmbedOrd (𝓊 ⁺) (𝓊 ⁺)
    EmbedOrd.carrier       h = Σ α ∶ Ord 𝓊 , ⟨ α ⟩ ≲ A
    EmbedOrd._≺_           h (α , _) (β , _) = α <ₒ β
    EmbedOrd.relation-prop h _ _ = <ₒ-prop _ _
    EmbedOrd.target        h = Ω
    EmbedOrd.embed         h = fst
    EmbedOrd.inj           h = Σ≡Prop λ α → squash₁
    EmbedOrd.pres≺         h _ _ = idfun _
    EmbedOrd.formsInitSeg  h β (α′ , le) β<ₒα′ = (β , ∥∥₁-map H le) , β<ₒα′ , refl
      where
      H : ⟨ α′ ⟩ ↪ A → Σ (⟨ β ⟩ → A) injective
      H (f , f-inj) = f ∘ g , g-inj ∘ f-inj where
        g = <→≤ β<ₒα′ .fst
        g-inj = IsOrdEmbed.inj $ <→≤ β<ₒα′ .snd
```

```agda
  ¬ℌ↪ : ⦃ _ : PR ⦄ → ¬ ⟨ ℌ ⟩ ↪ A
  ¬ℌ↪ F@(f , f-inj) = ¬α≃ₒα↓a ℌ h $
    ℌ       ≃ₒ˘⟨ ℌ⁻≃ₒℌ ⟩
    ℌ⁻      ≃ₒ⟨ α≃Ω↓α ⟩
    Ω ↓ ℌ⁻  ≃ₒ⟨ isoToEquiv j , mkIsOrderEquiv ordEquiv ⟩
    ℌ ↓ h   ≃ₒ∎
    where
    B : Type 𝓊
    B = Σ y ∶ A , ⟨ Resize {𝓋 = 𝓊} $ P y ⟩
      where
      P : A → hProp (𝓊 ⁺)
      P y = fiber f y , hasPropFb y
        where
        hasPropFb : hasPropFibers f
        hasPropFb _ (a , p) (b , q) = Σ≡Prop (λ _ → Aset _ _) (f-inj $ p ∙ sym q)
    i : Iso B ⟨ ℌ ⟩
    Iso.fun i (y , H) = unresize H .fst
    Iso.inv i x = f x , resize (x , refl)
    Iso.leftInv i (y , H) = Σ≡Prop (λ _ → isPropResize) (unresize H .snd)
    Iso.rightInv i a = Σ≡Prop (λ _ → squash₁) $ cong fst H where
      H : fst (unresize (resize _)) ≡ a
      H = subst (λ - → fst - ≡ _) (sym $ retIsEq isEquivResize _) refl
    ℌ⁻ : Ord 𝓊
    ℌ⁻ = ResizeOrd B ℌ $ isoToEquiv i
    ℌ⁻≃ₒℌ : ℌ⁻ ≃ₒ ℌ
    ℌ⁻≃ₒℌ = ResizeOrdEquiv B ℌ (isoToEquiv i)
    ℌ⁻≲A : ⟨ ℌ⁻ ⟩ ≲ A
    ℌ⁻≲A = ≈-≲-trans ∣ ℌ⁻≃ₒℌ .fst ∣₁ ∣ F ∣₁
    h : ⟨ ℌ ⟩
    h = ℌ⁻ , ℌ⁻≲A
    j : Iso ⟨ Ω ↓ ℌ⁻ ⟩ ⟨ ℌ ↓ h ⟩
    Iso.fun j (α , α≺ℌ) = (α , α≲A) , α≺ℌ
      where α≲A = ≲-trans ∣ <→↪ α≺ℌ ∣₁ ℌ⁻≲A
    Iso.inv j ((α , _) , α≺ℌ) = α , α≺ℌ
    Iso.rightInv j _ = Σ≡Prop (λ _ _ → <ₒ-prop _ _ _) (Σ≡Prop (λ _ → squash₁) refl)
    Iso.leftInv j _ = Σ≡Prop (λ _ _ → <ₒ-prop _ _ _) refl
    ordEquiv : ∀ x y → x ≺⟨ Ω ↓ ℌ⁻ ⟩ y ≃ (Iso.fun j) x ≺⟨ ℌ ↓ h ⟩ (Iso.fun j) y
    ordEquiv _ _ = idEquiv _
```

```agda
  <ℌ→≲A : ∀ α → α <ₒ ℌ → ⟨ α ⟩ ≲ A
  <ℌ→≲A α ((β , β≲) , eq) = ∥∥₁-map (↪-trans α↪β) β≲
    where
    f : ⟨ ℌ ↓ (β , β≲) ⟩ → ⟨ β ⟩
    f (_ , b , _) = b
    f-inj : injective f
    f-inj {(γ , _) , a , β↓a≡γ} {(δ , _) , b , β↓b≡δ} a≡b =
      Σ≡Prop (λ _ → <ₒ-prop _ _) (Σ≡Prop (λ _ → squash₁) γ≡δ) where
      γ≡δ = sym β↓a≡γ ∙ cong (β ↓_) a≡b ∙ β↓b≡δ
    α↪β : ⟨ α ⟩ ↪ ⟨ β ⟩
    α↪β = subst (λ α → ⟨ α ⟩ ↪ ⟨ β ⟩) eq (f , f-inj)
```

## 阿列夫层级

```agda
𝓊ₙ : ℕ → Level
𝓊ₙ zero = 𝓊₀
𝓊ₙ (suc n) = (𝓊ₙ n) ⁺
```

```agda
ℵ : (n : ℕ) → Card (𝓊ₙ n)
ℵ zero = ∣ ℕ , isSetℕ ∣
ℵ (suc n) = ∥∥₂-map (λ a → ⟨ Hartogs.ℌ ⟨ a ⟩ (str a) ⟩ , ordSet) (ℵ n)
```

```agda
module Omega (ordStrℕ : OrdStr ℕ) where
  ω : (n : ℕ) → Ord (𝓊ₙ n)
  ω zero = ℕ , ordStrℕ
  ω (suc n) = Hartogs.ℌ ⟨ ω n ⟩ ordSet
```
