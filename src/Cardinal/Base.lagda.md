---
title: 泛等结构集合论 (7) 构造主义阿列夫层级
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
zhihu-url: https://zhuanlan.zhihu.com/p/651332545
---

# 泛等结构集合论 (7) 构造主义阿列夫层级

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
  renaming ( _≤_ to _≤ₒ_; ≤-prop to ≤ₒ-prop)
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

基数的序 `_≤ₕ_` 是少有的必须直接取值到 `hProp` 上的情况, 也就是说我们要定义二元关系 `Card 𝓊 → Card 𝓋 → hProp (𝓊 ⊔ 𝓋)`.

```agda
_≤ₕ_ : Card 𝓊 → Card 𝓋 → hProp (𝓊 ⊔ 𝓋)
```

对于具体定义, 我们用 `∣∣-rec2` 转化为定义关于 `hSet` 的二元关系 `hSet 𝓊 → hSet 𝓋 → hProp (𝓊 ⊔ 𝓋)`. 然后对两个参数分别取左边, 得到两个类型 `A : Type 𝓊` 和 `B : Type 𝓋`, 它们对应两个基数的底类型, 而这两个基数的序就定义为它们对应底类型的势小于等于关系 `A ≲ B`. 由于它就是 `A` 到 `B` 的单射的命题截断, 所以配合上 `squash₁` 就可以组装成一个 `hProp`.

```agda
_≤ₕ_ = ∣∣-rec2 λ (A , _) (B , _) → A ≲ B , squash₁
```

对 `_≤ₕ_` 取左右投影就得到了通常的取值到 `Type` 的二元关系 `_≤_` 及其是命题的证据.

```agda
_≤_ : Card 𝓊 → Card 𝓋 → Type (𝓊 ⊔ 𝓋)
κ ≤ μ = ⟨ κ ≤ₕ μ ⟩

≤-prop : (κ : Card 𝓊) (μ : Card 𝓋) → isProp (κ ≤ μ)
≤-prop κ μ = str (κ ≤ₕ μ)
```

命题都是集合, 所以 `_≤_` 也是集合.

```agda
≤-set : (κ : Card 𝓊) (μ : Card 𝓋) → isSet (κ ≤ μ)
≤-set κ μ = isProp→isSet (≤-prop κ μ)
```

`_≤_` 的自反性和传递性由 `≲` 的自反性和传递性立即得到. 注意这里要用 `∥∥₂-elim` 将基数消去到 `_≤_`, 由于 `_≤_` 是集合所以没有问题.

```agda
≤-refl : (κ : Card 𝓊) → κ ≤ κ
≤-refl = ∥∥₂-elim (λ _ → ≤-set _ _) λ _ → ≲-refl

≤-trans : (κ : Card 𝓊) (μ : Card 𝓋) (ν : Card 𝓌) → κ ≤ μ → μ ≤ ν → κ ≤ ν
≤-trans = ∥∥₂-elim (λ _ → isSetΠ2 λ _ _ → isSet→ $ isSet→ $ ≤-set _ _)
  λ _ → ∥∥₂-elim2 (λ _ _ → isSet→ $ isSet→ $ ≤-set _ _) λ _ _ → ≲-trans
```

`_≤_` 的反对称性 (即施罗德-伯恩斯坦定理) 依赖于排中律.

## 哈特格斯数

一个集合的哈特格斯数是不能单射到该集合的最小序数. 我们将在**构造主义**下证明这样的序数对任意集合都存在.

首先给定位于宇宙 `𝓊` 的集合 `A`.

```agda
module Hartogs (A : Type 𝓊) (Aset : isSet A) where
```

我们发现, 如果坚持构造主义, `A` 的哈特格斯数将不得不位于序数宇宙 `𝓊 ⁺`. 这里发生的跨宇宙是构造主义哈特格斯数的主要局限所在, 也是证明其性质的主要难点所在. 除此之外, 在泛等基础下的处理都较传统简单.

跨宇宙的根本原因是, 哈特格斯数的构造要求我们收集序数宇宙 `𝓊` 中满足一定条件 `P` 的序数组成底集 `carrier`, 也就是说 `carrier` 需要定义为类型 `Σ (Ord 𝓊) P`. 这时, 因为 `Ord 𝓊` 本身位于 `𝓊 ⁺`, 所以 `carrier` 将不得不位于 `𝓊 ⁺`.

一个貌似可行的解决方法是我们对 `A : Type (𝓊 ⁺)` 收集 `Ord 𝓊` 中的序数, 这样 `carrier` 位于 `𝓊 ⁺`, 与 `A` 同级. 但是这会导致无法证明 `carrier` 不能单射到 `A`. 后面我们会看到该证明正好依赖于 `A` 比 `carrier` 低一个层级. 可能还有其他解决方案, 但我们暂时没有想到.

回到 `carrier` 的定义, 我们要收集的序数 `α : Ord 𝓊` 必须满足势小于等于 `A`, 它们所组成的序数就满足哈特格斯数的定义, 即不能单射到 `A` 的最小序数.

```agda
  carrier : Type (𝓊 ⁺)
  carrier = Σ α ∶ Ord 𝓊 , ⟨ α ⟩ ≲ A
```

**定理** `carrier` 构成一个序数 (我们命名为 `ℌ`).  
**证明** 我们采用嵌入序数的方式, 把 `carrier` 嵌入到 `Ω`, 以说明它可以构成序数.

```agda
  ℌ : Ord (𝓊 ⁺)
  ℌ = tieup h
    where
    h : EmbedOrd (𝓊 ⁺) (𝓊 ⁺)
    EmbedOrd.carrier       h = carrier
    EmbedOrd.target        h = Ω
```

`carrier` 元素间的序遵循依值配对左边的序数的序.

```agda
    EmbedOrd._≺_           h (α , _) (β , _) = α < β
    EmbedOrd.relation-prop h _ _ = <-prop _ _
```

`carrier` 嵌入到 `Ω` 的方式就是取依值配对的左边 `fst`. 因为右边是命题, 所以 `fst` 是单射. 又因为序也遵循左边的序, 所以保序性是显然的.

```agda
    EmbedOrd.embed         h = fst
    EmbedOrd.inj           h = Σ≡Prop λ α → squash₁
    EmbedOrd.pres≺         h _ _ = idfun _
```

最后我们需要说明 `fst` 能形成前段. 给定 `β < α′`, 其中 `⟨ α′ ⟩` 的势小于等于 `A`, 我们说明 `⟨ β ⟩` 的势也小于等于 `A`, 以配合 `β` 组成所需的前段元素.

只需证 `⟨ α′ ⟩ ↪ A` 蕴含 `⟨ β ⟩ ↪ A`, 然后就可以用 `∥∥₁-map` 得到 `⟨ α′ ⟩ ≲ A` 蕴含 `⟨ β ⟩ ≲ A`.

```agda
    EmbedOrd.formsInitSeg  h β (α′ , le) β<α′ = (β , ∥∥₁-map H le) , β<α′ , refl
      where
      H : ⟨ α′ ⟩ ↪ A → ⟨ β ⟩ ↪ A
```

因为 `β < α′`, 我们可以从中取出 `⟨ β ⟩` 到 `⟨ α′ ⟩` 的单射, 将它与 `⟨ α′ ⟩` 到 `A` 的单射复合, 就得到了 `⟨ β ⟩` 到 `A` 的单射. ∎

```agda
      H (f , f-inj) = f ∘ g , g-inj ∘ f-inj where
        g = <→≤ β<α′ .fst
        g-inj = IsOrdEmbed.inj $ <→≤ β<α′ .snd
```

**定理** (PR). 哈特格斯数的底集 `⟨ ℌ ⟩` 不能单射到 `A`.  
**证明概要** 假设 `f` 是 `⟨ ℌ ⟩` 到 `A` 的单射, 我们要推出矛盾 (注意这里并不需要依赖排中律的反证法). 首先我们说明整体思路, 然后再逐步展开.

整体思路是, 对于 `ℌ : Ord (𝓊 ⁺)`, 我们利用 `f` 构造一个 `ℌ⁻ : Ord 𝓊`, 并证明它们等价. 由前提 `⟨ ℌ ⟩ ≲ A` 有 `⟨ ℌ⁻ ⟩ ≲ A`.

这样的话 `h = (ℌ⁻ , ℌ⁻≲A)` 构成了一个 `⟨ ℌ ⟩`. 我们证明 `Ω ↓ ℌ⁻ ≃ₒ ℌ ↓ h`, 从而得到 `ℌ` 等价于其前段 `ℌ ↓ h`, 矛盾. ∎

```agda
  ¬ℌ↪ : ⦃ _ : PR ⦄ → ¬ ⟨ ℌ ⟩ ↪ A
  ¬ℌ↪ F@(f , f-inj) = ¬α≃ₒα↓a ℌ h $
    ℌ       ≃ₒ˘⟨ ℌ⁻≃ₒℌ ⟩
    ℌ⁻      ≃ₒ⟨ α≃Ω↓α ⟩
    Ω ↓ ℌ⁻  ≃ₒ⟨ isoToEquiv j , mkIsOrderEquiv ordEquiv ⟩
    ℌ ↓ h   ≃ₒ∎
    where
```

**注意** 这一思路依赖于 `A` 的等级比 `⟨ ℌ ⟩` 低一级. 如果它们同级, 我们不知道如何在不使用排中律的情况下使 `ℌ` 降级. 而拿到降级的 `ℌ⁻` 是构造矛盾的关键, 不能降级的话似乎**没有矛盾**.

**证明细节** 首先我们构造单射 `f` 的值域 `B : Type 𝓊`, 它由能构成 `f` 的纤维 `fiber f y` 的那些 `y : A` 组成. 注意纤维本身位于 `𝓊 ⁺`, 但由 `A` 的集合性以及 `f` 的单射性保证了纤维是命题, 所以可以用 `PR` 降级到 `𝓊`.

```agda
    B : Type 𝓊
    B = Σ y ∶ A , ⟨ Resize {𝓋 = 𝓊} $ P y ⟩
      where
      P : A → hProp (𝓊 ⁺)
      P y = fiber f y , hasPropFb y
        where
        hasPropFb : hasPropFibers f
        hasPropFb _ (a , p) (b , q) = Σ≡Prop (λ _ → Aset _ _) (f-inj $ p ∙ sym q)
```

因为 `B` 是单射的值域, 它与 `⟨ ℌ ⟩` 有双射是显然的. 技术上只需注意处理一下对纤维降级导致的 `unresize (resize _)` 式, 它们由互逆可以化简掉.

```agda
    i : Iso B ⟨ ℌ ⟩
    Iso.fun i (y , H) = unresize H .fst
    Iso.inv i x = f x , resize (x , refl)
    Iso.leftInv i (y , H) = Σ≡Prop (λ _ → isPropResize) (unresize H .snd)
    Iso.rightInv i a = Σ≡Prop (λ _ → squash₁) $ cong fst H where
      H : fst (unresize (resize _)) ≡ a
      H = subst (λ - → fst - ≡ _) (sym $ retIsEq isEquivResize _) refl
```

回想我们有序数降级: 任意 `β : Ord 𝓋` 可以降级到 `Ord 𝓊` 上, 只要找到一个 `A : Type 𝓊` 满足 `A ≃ ⟨ β ⟩`.

```agda
    _ : (A : Type 𝓊) (β : Ord 𝓋) → A ≃ ⟨ β ⟩ → Ord 𝓊
    _ = ResizeOrd
```

令其中的 `β = ℌ`, `A = B`, 就得到了降级哈特格斯数 `ℌ⁻ : Ord 𝓊`, 它与原 `ℌ : Ord (𝓊 ⁺)` 等价.

```agda
    ℌ⁻ : Ord 𝓊
    ℌ⁻ = ResizeOrd B ℌ $ isoToEquiv i
    ℌ⁻≃ₒℌ : ℌ⁻ ≃ₒ ℌ
    ℌ⁻≃ₒℌ = ResizeOrdEquiv B ℌ (isoToEquiv i)
```

由势的传递性我们有 `⟨ ℌ⁻ ⟩ ≲ A`.

```agda
    ℌ⁻≲A : ⟨ ℌ⁻ ⟩ ≲ A
    ℌ⁻≲A = ≈-≲-trans ∣ ℌ⁻≃ₒℌ .fst ∣₁ ∣ F ∣₁
```

于是 `ℌ⁻` 配备上 `⟨ ℌ⁻ ⟩ ≲ A` 的证据就构成了 `ℌ` 底集 `⟨ ℌ ⟩`, 也即 `carrier` 的一个项.

```agda
    h : ⟨ ℌ ⟩
    h = ℌ⁻ , ℌ⁻≲A
```

接着我们要证明 `⟨ Ω ↓ ℌ⁻ ⟩` 等价于 `⟨ ℌ ↓ h ⟩`, 从而得到 `⟨ ℌ ⟩` 等价与 `⟨ ℌ ↓ h ⟩` 的矛盾.

- 左边到右边: 给定 `⟨ Ω ↓ ℌ⁻ ⟩`, 可以解构出 `α : Ord 𝓊` 以及 `α < ℌ` 的证据. 由 `_≲_` 的传递性, `α ≲ ℌ ≈ ℌ⁻ ≲ A`, 所以 `(α , α≲A)` 正是 `⟨ ℌ ⟩` 的项. 又有 `α < ℌ` 的证据, `((α , α≲A) , α≺ℌ)` 即是所需 `⟨ ℌ ↓ h ⟩` 的项.
- 右边到左边: 给定 `⟨ ℌ ↓ h ⟩`, 可以解构出 `α : Ord 𝓊` 以及 `α < ℌ` 的证据, 配对成 `⟨ Ω ↓ ℌ⁻ ⟩` 的项即可.
- 左右逆: 除掉配对中不影响相等的命题, 等号两边剩下的数据是自反的.

```agda
    j : Iso ⟨ Ω ↓ ℌ⁻ ⟩ ⟨ ℌ ↓ h ⟩
    Iso.fun j (α , α≺ℌ) = (α , α≲A) , α≺ℌ
      where α≲A = ≲-trans ∣ <→↪ α≺ℌ ∣₁ ℌ⁻≲A
    Iso.inv j ((α , _) , α≺ℌ) = α , α≺ℌ
    Iso.rightInv j _ = Σ≡Prop (λ _ _ → <-prop _ _ _) (Σ≡Prop (λ _ → squash₁) refl)
    Iso.leftInv j _ = Σ≡Prop (λ _ _ → <-prop _ _ _) refl
```

最后我们要说明 `Iso.fun j` 是序等价, 观察定义可知这也是自反的. ∎

```agda
    ordEquiv : ∀ x y → x ≺⟨ Ω ↓ ℌ⁻ ⟩ y ≃ (Iso.fun j) x ≺⟨ ℌ ↓ h ⟩ (Iso.fun j) y
    ordEquiv _ _ = idEquiv _
```

**定理** 比哈特格斯数小的序数都可以单射到 `A`.  
**证明** 给定 `α < ℌ`, 由序数小于的定义, 可以解构出一个 `b@(β , β≲) : ⟨ ℌ ⟩` 满足 `α ≡ ℌ ↓ b`, 其中 `b` 又可以解构出一个 `β : Ord 𝓊` 满足 `⟨ β ⟩ ≲ A`.

只要构造出一个 `⟨ α ⟩ ↪ ⟨ β ⟩`, 就可以由势的传递性证明目标 `⟨ α ⟩ ≲ A`.

```agda
  <ℌ→≲A : ∀ α → α < ℌ → ⟨ α ⟩ ≲ A
  <ℌ→≲A α (b@(β , β≲) , eq) = ∥∥₁-map (↪-trans α↪β) β≲
    where
```

由于 `α ≡ ℌ ↓ b`, 我们构造 `⟨ ℌ ↓ b ⟩` 到 `⟨ β ⟩` 的单射 `f` 即可.

`f` 的构造如下: 给定一个 `⟨ ℌ ↓ b ⟩`, 可以解构出 `x : ⟨ β ⟩`, 它就是所需的 `⟨ β ⟩`.

```agda
    α↪β : ⟨ α ⟩ ↪ ⟨ β ⟩
    α↪β = subst (λ α → ⟨ α ⟩ ↪ ⟨ β ⟩) eq (f , f-inj)
      where
      f : ⟨ ℌ ↓ b ⟩ → ⟨ β ⟩
      f (_ , x , _) = x
```

最后我们要说明 `f` 是单射. 给定 `⟨ ℌ ↓ b ⟩` 的两个项, 可以解构出两个序数 `γ δ : Ord 𝓊` 以及 `⟨ β ⟩` 两个项 `x y : ⟨ β ⟩`, 满足 `β ↓ x ≡ γ` 以及 `β ↓ y ≡ δ`, 且 `f` 作用与它们之后得到的结果相等, 即 `x ≡ y`. 要证 `⟨ ℌ ↓ b ⟩` 的这两个项相等.

```agda
      f-inj : injective f
      f-inj {(γ , _) , x , β↓x≡γ} {(δ , _) , y , β↓y≡δ} x≡y =
```

除去命题分量, 我们只需要证 `γ ≡ δ`. 由于 `β ↓ x ≡ γ` 以及 `β ↓ y ≡ δ`, 只需证 `β ↓ x ≡ β ↓ y`, 由前提 `x ≡ y` 即证. ∎

```agda
        Σ≡Prop (λ _ → <-prop _ _) (Σ≡Prop (λ _ → squash₁) γ≡δ) where
        γ≡δ = sym β↓x≡γ ∙ cong (β ↓_) x≡y ∙ β↓y≡δ
```

以上两条定理就说明了 `ℌ` 是不能单射到 `A` 的最小序数.

## 阿列夫层级

从 `ℕ` 开始, 取其基数 `∣ ℕ , isSetℕ ∣`, 对其迭代哈特格斯函数, 就可以构造阿列夫层级.

由于构造主义下每取一次哈特格斯数都会提高一个宇宙层级, 而宇宙只有可数层, 所以只能表示出可数个阿列夫数.

```agda
ℵ : (n : ℕ) → Card (𝓊ₙ n)
ℵ zero = ∣ ℕ , isSetℕ ∣
ℵ (suc n) = ∥∥₂-map (λ a → ⟨ Hartogs.ℌ ⟨ a ⟩ (str a) ⟩ , ordSet) (ℵ n)
```

注意阿列夫层级是基数层级, 它与序数层级 `ωₙ` 的类型是不一样的.

```agda
-- 我们懒得写出自然数有良序的证明了
module Omega (ordStrℕ : OrdStr ℕ) where
  ω : (n : ℕ) → Ord (𝓊ₙ n)
  ω zero = ℕ , ordStrℕ
  ω (suc n) = Hartogs.ℌ ⟨ ω n ⟩ ordSet
```

## 考察

按照构造主义的程度, 粗略地, 可以分为以下5种等级.

- -1级: 反经典理论, 例如综合可计算理论的背景理论, 有效意象的内逻辑.
- 0级: 兼容经典的纯构造性理论, 例如立方类型论.
- 1级: 大部分性质可构造性证明的领域, 例如直觉主义分析学, 直觉主义序数理论.
- 2级: 核心性质可构造性证明的领域, 例如本文讲的哈特格斯数.
- 3级: 可构造性定义, 但其性质的证明几乎都依赖排中律的领域, 例如本文讲的阿列夫层级.
