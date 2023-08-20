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

本讲我们介绍泛等基础如何处理集合论中的另一个重要概念: 基数. 简单来说, 每个集合 `a : hSet 𝓊` 本身几乎可以视作它自己的基数. 因为同构 (也就是能建立双射) 的集合在泛等基础中是相等的. 这正是 `hSet` 上的泛等原理所说:

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

另外我们还是需要搭配序数的概念来做一些构造, 但这里把 `≤` 相关的命名空间让出来, 因为基数也有自己的序.

```agda
open import Ordinal hiding (≤-refl; ≤-trans)
  renaming ( _≤_ to _≤ₒ_; ≤-prop to ≤ₒ-prop
           ; _<_ to _<ₒ_; <-prop to <ₒ-prop)
open BinaryRelation
```

## 基数

我们曾大费周折地定义了序数宇宙. 而基数宇宙的定义则相当简单粗暴, 它就是集合宇宙的集合截断. 上面说了集合宇宙本身不是集合, 但我们希望它是, 所以对它做集合截断, 这样就完成了定义基数宇宙的全部工作.

```agda
Card : (𝓊 : Level) → Type (𝓊 ⁺)
Card 𝓊 = ∥ hSet 𝓊 ∥₂
```

基数的项由集合截断的构造子 `∣_∣` 给出, 它与传统上取基数的符号相似应该是一个巧合.

```agda
_ : hSet 𝓊 → Card 𝓊
_ = ∣_∣
```

如所期望的那样, 基数宇宙是一个集合, 证据由集合截断的构造子 `squash₂` 给出.

```agda
isSetCard : isSet (Card 𝓊)
isSetCard = squash₂
```

运用集合截断的 `∥∥₂-rec`, 可以将关于基数的命题归结为关于集合的命题.

```agda
∣∣-rec : (hSet 𝓊 → hProp 𝓋) → Card 𝓊 → hProp 𝓋
∣∣-rec P = ∥∥₂-rec isSetHProp P

∣∣-rec2 : (hSet 𝓊 → hSet 𝓋 → hProp 𝓌) → Card 𝓊 → Card 𝓋 → hProp 𝓌
∣∣-rec2 P = ∥∥₂-rec2 isSetHProp P
```

基数的相等是命题, 但集合的相等不是, 所以一般上它们无法直接同构. 但只要对集合的相等做命题截断, 就能保证它们同构. 这一性质完全刻画了基数的概念, 甚至比传统上的更强. 传统上只是说基数相等当且仅当集合等势. 但在泛等基础中, 等势就意味着相等, 只不过这个相等是带着命题截断的. 回想我们在[前置知识](https://zhuanlan.zhihu.com/p/649742992)中把等势定义为等价的命题截断, 所以只要在泛等原理的等价两边同时做命题截断就有这个结论.

接下来的内容是以上非形式讨论的形式化.

**引理** 基数相等与集合相等的命题截断同构.  
**证明**

- 左边到右边: 右边是关于集合的命题, 它可以视作是由关于基数的命题归结而来. 于是我们可以用左边去改写该命题, 然后用自反性得证.

```agda
cardEqIso∥SetEq∥ : {a b : hSet 𝓊} → Iso (∣ a ∣ ≡ ∣ b ∣) ∥ a ≡ b ∥₁
Iso.fun (cardEqIso∥SetEq∥ {𝓊} {b}) p = subst (λ κ → ∣∣-rec (λ a → ∥ a ≡ b ∥ₚ) κ .fst) (sym p) ∣ refl ∣₁
```

- 右边到左边: 由于左边是命题, 用命题截断的 `∥∥₁-rec`, 只需证 `a ≡ b → ∣ a ∣ ≡ ∣ b ∣`, 两边同时取 `∣_∣` 即可.
- 右逆: 要证的等式两边都是命题截断的 `∥ a ≡ b ∥₁` 的证明, 用 `squash₁` 即证.
- 左逆: 要证的等式两边都是基数相等的证明, 用基数宇宙是集合的证据即证. ∎

```agda
Iso.inv       cardEqIso∥SetEq∥ = ∥∥₁-rec (isSetCard _ _) (cong ∣_∣)
Iso.rightInv  cardEqIso∥SetEq∥ _ = squash₁ _ _
Iso.leftInv   cardEqIso∥SetEq∥ _ = isSetCard _ _ _ _
```

**引理** 对带有结构 `S : Type 𝓊 → Type 𝓋` 的类型 `TypeWithStr 𝓊 S`, 只要结构是命题性的 (`∀ x → isProp (S x)`), 那么对任意 `a b : TypeWithStr 𝓊 S` 有 `∥ a ≡ b ∥₁` 与 `⟨ a ⟩ ≈ ⟨ b ⟩` 同构.  
**证明**

- 左边到右边: 两边都是命题截断, 用 `∥∥₁-map` 对两边同时消去截断, 只需证结构相等蕴含底类型等价, 改写即证.

```agda
∥eq∥IsoEquivp : {S : Type 𝓊 → Type 𝓋} {a b : TypeWithStr 𝓊 S} →
  (∀ x → isProp (S x)) → Iso ∥ a ≡ b ∥₁ (⟨ a ⟩ ≈ ⟨ b ⟩)
Iso.fun (∥eq∥IsoEquivp _) = ∥∥₁-map λ a≡b → subst (λ b → _ ≃ ⟨ b ⟩) a≡b (idEquiv _)
```

- 右边到左边: 同样对两边同时消去截断, 只需证底类型等价蕴含结构相等. 由前提, 结构是命题性的, 只需证底类型相等, 由 `ua` 即证.
- 左右逆: 由于两边都是命题, 用 `squash₁` 即证. ∎

```agda
Iso.inv       (∥eq∥IsoEquivp Sprop) = ∥∥₁-map λ a≃b → Σ≡Prop Sprop (ua a≃b)
Iso.rightInv  (∥eq∥IsoEquivp _) _ = squash₁ _ _
Iso.leftInv   (∥eq∥IsoEquivp _) _ = squash₁ _ _
```

**定理** 基数相等等价于集合等势.  
**证明** 将上两个引理所说的同构转化为等价, 再用等价的复合连起来即可. ∎

```agda
cardEq≃Equivp : {a b : hSet 𝓊} → (∣ a ∣ ≡ ∣ b ∣) ≃ (⟨ a ⟩ ≈ ⟨ b ⟩)
cardEq≃Equivp = compEquiv
  (isoToEquiv cardEqIso∥SetEq∥)
  (isoToEquiv $ ∥eq∥IsoEquivp λ _ → isPropΠ2 λ _ _ → isPropIsProp)
```

## 基数的序

```agda
_≤ₕ_ : Card 𝓊 → Card 𝓋 → hProp (𝓊 ⊔ 𝓋)
_≤ₕ_ = ∣∣-rec2 λ (A , _) (B , _) → A ≲ B , squash₁
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
