---
title: 泛等结构集合论 (2) 前置知识
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
zhihu-url: https://zhuanlan.zhihu.com/p/649742992
---

# 泛等结构集合论 (2) 前置知识

> 交流Q群: 893531731  
> 本文源码: [Preliminary.lagda.md](https://github.com/choukh/USST/blob/main/src/Preliminary.lagda.md)  
> 高亮渲染: [Preliminary.html](https://choukh.github.io/USST/Preliminary.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module Preliminary where
open import Cubical public
```

我们在上一章 [泛等结构集合论 (1) 泛等基础](https://zhuanlan.zhihu.com/p/643059692) 介绍了直接从 Cubical 标准库中导入的概念, 而本章着重介绍标准库中没有的前置知识.

我们约定使用 `A` `B` `C` `X` `Y` 表示任意层级的类型.

```agda
private variable A B C X Y : Type 𝓊
```

## 命题逻辑

首先我们来补充泛等基础中对应于直觉主义命题逻辑的相关概念.

### 真值

我们用表示 `⟦⊥⟧` 假命题, 用表示 `⟦⊤⟧` 真命题.
⟦⊥⟧
```agda
⟦⊥⟧ : hProp 𝓊
⟦⊥⟧ = ⊥* , isProp⊥*

⟦⊤⟧ : hProp 𝓊
⟦⊤⟧ = ⊤* , isProp⊤*
```

以下是无矛盾律在直觉主义中更容易处理的版本. 因为我们无法证明排中律 "`A` 或 `¬ A`", 所以单有 `A → ¬ A → ⊥` 也无法推出矛盾, 必须采用下面的形式才行.

```agda
noncontradiction : (A → ¬ A) → (¬ A → A) → ⊥
noncontradiction p q = p (q λ a → p a a) (q λ a → p a a)
```

### 析取

逻辑析取定义为**和类型 (sum type)** 的命题截断. 因为和类型的项起码有两种 (左边或右边) 不同的构造方式, 但析取不关心具体是哪种, 所以必须要做命题截断, 以确保所有证明项都相等.

```agda
import Cubical.Data.Sum
module ⊎ = Cubical.Data.Sum
open ⊎ public using (_⊎_)

infixr 2 _∨_
_∨_ : Type 𝓊 → Type 𝓋 → Type _
A ∨ B = ∥ A ⊎ B ∥₁
```

以下是析取的引入规则, 注意它的证明中使用了命题截断的构造子 `∣_∣₁`.

```agda
inl : A → A ∨ B
inl x = ∣ ⊎.inl x ∣₁

inr : B → A ∨ B
inr x = ∣ ⊎.inr x ∣₁
```

注意我们不需要对积类型做命题截断以得到合取, 因为当 `_×_` 的两边都是命题的时候, 它的项只有一种构造方式, 所以它们之间的相等是自然成立的.

### 逻辑等价

命题 `A` 与 `B` 逻辑等价 `_↔_` 定义为 `A` 蕴含 `B` 且 `B` 蕴含 `A`, 它有两种构造方式: 先证左边再证右边 `→:_←:_` 或者先证右边再证左边 `←:_→:_`.

`_↔⟨_⟩_` 等记法与上一章讲的 `_≡⟨_⟩_` 等类似, 它允许我们写"当且仅当"推导链, 使证明过程更加清晰.

`isProp↔` 说明逻辑等价是命题. `hPropExt` 是命题的外延性, 它说两个等价的命题相等, 这得益于泛等原理.

```agda
open import CubicalExt.Iff public
  using ( _↔_; to; from; →:_←:_; ←:_→:_
        ; _↔⟨_⟩_; _↔˘⟨_⟩_; _↔≡⟨_⟩_; _↔≡˘⟨_⟩_; _↔⟨⟩_; _↔∎
        ; isProp↔; hPropExt
        )
```

## 单射

标准库里对单射的定义是为高阶同伦类型改编过的版本, 叫同伦嵌入 `isEmbedding`. 对于集合层面的数学我们用传统的单射性定义就够了.

```agda
injective : (A → B) → Type _
injective f = ∀ {x y} → f x ≡ f y → x ≡ y
```

`isEquiv→isEmbedding` 说同伦等价都是同伦嵌入, 又 `isEmbedding→Inj` 说同伦嵌入都是单射, 所以同伦等价都是单射.

```agda
open import Cubical.Functions.Embedding using (isEmbedding; isEquiv→isEmbedding; isEmbedding→Inj)

equivFunInjective : (f : A ≃ B) → injective (f ⁺¹)
equivFunInjective f = isEmbedding→Inj (isEquiv→isEmbedding (snd f)) _ _
```

库中还有比单射更强的一种概念是说 `B` 的每一点的纤维都是命题, 它蕴含同伦嵌入.

```agda
open import Cubical.Foundations.Equiv public using (fiber)
open import Cubical.Functions.Embedding public using (hasPropFibers; hasPropFibers→isEmbedding)
```

我们将 `A` 到 `B` 的单射的全体记作 `A ↪ B`. 注意这里用的是Σ类型, 并没有做命题截断, 有时候延迟截断会更方便处理.

```agda
_↪_ : Type 𝓊 → Type 𝓋 → Type _
A ↪ B = Σ (A → B) injective
```

`↪` 构成一个预序.

```agda
↪-refl : A ↪ A
↪-refl = idfun _ , λ refl → refl

↪-trans : A ↪ B → B ↪ C → A ↪ C
↪-trans (f , f-inj) (g , g-inj) = g ∘ f , f-inj ∘ g-inj
```

`↪` 的反对称性 (即施罗德-伯恩斯坦定理) 依赖于排中律. 虽然我们不能从双向单射得到等价, 但可以从等价可以得到双向单射.

```agda
≃→↪ : A ≃ B → A ↪ B
≃→↪ f = f ⁺¹ , equivFunInjective f
```

## 满射

对于满射我们直接使用库中的定义, 只是改了一下名字使得命名风格统一.

```agda
open import Cubical.Functions.Surjection public renaming (isSurjection to surjective)
```

传统说法是说对任意 `y` 都**存在** `x` 使得 `f x ≡ y`. 库中的定义是说任意 `y` 的纤维 `fiber f y` 的命题截断可证. 这两种定义是判断相等的.

`isEmbedding×isSurjection→isEquiv` 说明一个函数是同伦嵌入且满射, 那么它是同伦等价.

```agda
open import Cubical.Functions.Surjection public using (isEmbedding×isSurjection→isEquiv)
```

可以证明, 如果一个单射是射到集合的, 那么它是同伦嵌入.

```agda
injective→isEmbedding : {f : A → B} → isSet B → injective f → isEmbedding f
injective→isEmbedding Bset f-inj = hasPropFibers→isEmbedding
  λ { b (x , fx≡b) (y , fy≡b) → Σ≡Prop (λ _ → Bset _ _) (f-inj $ fx≡b ∙ sym fy≡b) }
```

所以对射到集合的函数, 可以复刻传统结果: 单射且满射蕴含双射.

```agda
inj→sur→isEquiv : {f : A → B} → isSet B → injective f → surjective f → isEquiv f
inj→sur→isEquiv Bset inj sur = isEmbedding×isSurjection→isEquiv $
  injective→isEmbedding Bset inj , sur
```

## 势

我们说类型 `A` 与 `B` **等势 (equipotent)**, 记作 `A ≈ B`, 当且仅当有 `∥ A ≃ B ∥₁`. 命题截断表示我们并不关系具体是哪个等价, 只要有等价就行.

```agda
_≈_ : Type 𝓊 → Type 𝓋 → Type _
A ≈ B = ∥ A ≃ B ∥₁
```

我们说类型 `A` 的势小于等于 `B`, 记作 `A ≲ B`, 当且仅当有 `∥ A ↪ B ∥₁`. 命题截断表示我们并不关系具体是哪个单射, 只要有单射就行.

```agda
infix 21 _≲_
_≲_ : Type 𝓊 → Type 𝓋 → Type _
A ≲ B = ∥ A ↪ B ∥₁

_≳_ : Type 𝓊 → Type 𝓋 → Type _
A ≳ B = B ≲ A

_≴_ : Type 𝓊 → Type 𝓋 → Type _
A ≴ B = ¬ A ≲ B
```

我们说 A 的势严格小于 B, 当且仅当 A 的势小于等于 B 且 B 的势不小于等于 A.

```agda
_⋨_ : Type 𝓊 → Type 𝓋 → Type _
A ⋨ B = A ≲ B × B ≴ A
```

由单射的预序性立即有势的预序性.

```agda
≲-refl : A ≲ A
≲-refl = ∣ ↪-refl ∣₁

≲-trans : A ≲ B → B ≲ C → A ≲ C
≲-trans = ∥∥₁-map2 ↪-trans
```

我们有传递性的变体:

```agda
≈-≲-trans : A ≈ B → B ≲ C → A ≲ C
≈-≲-trans = ∥∥₁-map2 λ A≃B B≲C → ↪-trans (≃→↪ A≃B) B≲C
```

## 幂集

给定任意类型 `X : Type 𝓊`, 我们把 `X` 到命题宇宙 `hProp 𝓊` 的函数叫做 `X` 的幂集, 记作 `ℙ X`, 它的项也叫 `X` 的子集.

给定项 `x : X` 和子集 `A : ℙ X`, 属于关系 `x ∈ A` 定义为 `⟨ A x ⟩`. `A` 是取值到 `hProp 𝓊` 的函数, 这保证了属于关系是取值到命题的. 此外, 可以证明幂集确实是一个集合: `isSetℙ`.

```agda
open import Cubical.Foundations.Powerset public
  using (ℙ; _∈_; _⊆_; ⊆-isProp; isSetℙ)
```

不属于符号 `_∉_` 定义为 `_∈_` 的否定, 即 `x ∉ A = ¬ x ∈ A`.

```agda
_∉_ : X → ℙ X → Type _
x ∉ A = ¬ x ∈ A
```

包含关系 `A ⊆ B` 的定义为 `∀ x → x ∈ A → x ∈ B`, 真包含 `A ⊂ B` 定义为 `A ⊆ B` 且存在 `x ∈ B` 但 `x ∉ A`.

```agda
_⊂_ : ℙ X → ℙ X → Type _
A ⊂ B = A ⊆ B × (∃ x ∶ _ , x ∈ B × x ∉ A)
```

`A ⊂ B` 是命题.

```agda
⊂-prop : {A B : ℙ X} → isProp (A ⊂ B)
⊂-prop = isProp× (⊆-isProp _ _) squash₁
```

我们用 `⟦ A ⟧` 表示幂集 `A` 所对应的Σ类型.

```agda
⟦_⟧ : {X : Type 𝓊} → ℙ X → Type 𝓊
⟦ A ⟧ = Σ _ (_∈ A)
```

### 迭代幂集

所谓迭代幂集, 就是指形如 `ℙ (ℙ ... (ℙ A))` 的幂集. 我们希望通过参数指定迭代次数, 但问题是每迭代一次会提高一次宇宙层级, 我们需要一个额外的函数 `ℓ` 迭代宇宙层级的后继 `_⁺`, 这样才能写出迭代幂集的合法类型签名.

```agda
ℓ : Level → ℕ → Level
ℓ 𝓊 zero = 𝓊
ℓ 𝓊 (suc n) = ℓ 𝓊 n ⁺
```

`ℓ` 可以指定初始层级, 如果指定为 `𝓊₀`, 则可以得到以下简化版本, 会在之后的一些构造中用到.

```agda
𝓊ₙ : ℕ → Level
𝓊ₙ = ℓ 𝓊₀
```

有了宇宙层级迭代函数 `ℓ` 之后, 迭代幂集的签名就可以写成 `(n : ℕ) → Type 𝓊 → Type (ℓ 𝓊 n ⁺)`, 其中 `n` 指 `suc n` 重幂集. 例如三重幂集的签名为 `Type 𝓊 → Type Type (𝓊 ⁺ ⁺ ⁺)`.

```agda
ℙ[_]⁺ : (n : ℕ) → Type 𝓊 → Type (ℓ 𝓊 n ⁺)
ℙ[ zero ]⁺ A = ℙ A
ℙ[ suc n ]⁺ A = ℙ (ℙ[ n ]⁺ A)
```

## 降级公理

降级公理, 也叫**命题宇宙降级 (propositional resizing)**, 简称PR. PR的宣告实际上等于是取消了命题宇宙的分层, 使得命题宇宙只有一层, 所有命题都位于那一层.

如果取消所有类型的分层, 那么将导致罗素悖论, 而只取消命题宇宙的分层则不会. 我们只会进入所谓**非直谓 (impredicative)** 的数学世界, 而经典数学都是这样的.

代码工程上, 我们使用了 record 类型, 它可以视作一种带了很多语法糖的Σ类型. 我们定义的 `PropositionalResizing` 包括了一个 `Resize` 函数, 以实现给定的两个命题宇宙的相互转换, 并且它需要满足 `resize` 和 `unresize` 性质, 即转换前后的两个命题逻辑等价.

```agda
record PropositionalResizing (𝓊 𝓋 : Level) : Type (𝓊 ⁺ ⊔ 𝓋 ⁺) where
  field
    Resize : hProp 𝓊 → hProp 𝓋
    resize : {P : hProp 𝓊} → ⟨ P ⟩ → ⟨ Resize P ⟩
    unresize : {P : hProp 𝓊} → ⟨ Resize P ⟩ → ⟨ P ⟩
```

对于命题来说, 逻辑等价意味着同伦等价, 也就是说 `resize` 和 `unresize` 都是同伦等价.

```agda
  module _ {P : hProp 𝓊} where
    ResizeEquiv : ⟨ P ⟩ ≃ ⟨ Resize P ⟩
    ResizeEquiv = isoToEquiv $ iso resize unresize (λ _ → (Resize P) .snd _ _) λ _ → P .snd _ _

    isEquivResize : isEquiv (resize {P = P})
    isEquivResize = ResizeEquiv .snd

    isEquivUnresize : isEquiv (unresize {P = P})
    isEquivUnresize = invEquiv ResizeEquiv .snd
```

降级命题是命题.

```agda
    isPropResize : isProp ⟨ Resize P ⟩
    isPropResize _ _ = equivFunInjective (invEquiv ResizeEquiv) (str P _ _)
```

以下代码是 Agda 的一些小技巧, 不熟悉 Agda 可以不用管. 只需知道我们只要在模块声明中以 `⦃ _ : PR ⦄` 的形式声明参数, 那么就等于假设了 PR, 就可以在该模块中尽情地使用上面的三个函数, 而不用显式说明具体是哪两个命题宇宙之间的转换.

```agda
PR = ∀ {𝓊 𝓋} → PropositionalResizing 𝓊 𝓋
open PropositionalResizing ⦃...⦄ public
```

两个降级命题间蕴含关系的证明可以通过它们底层类型间的映射来证明.

```agda
module _ ⦃ _ : PR ⦄ where
  resize∥∥-map : (A → B) → (⟨ Resize {𝓋 = 𝓊} ∥ A ∥ₚ ⟩ → ⟨ Resize {𝓋 = 𝓋} ∥ B ∥ₚ ⟩)
  resize∥∥-map f p = resize $ ∥∥₁-map f $ unresize p
```

## 降级幂集

在非直谓的设定下, 我们可以使用另一种幂集的定义 `ℙ[_]`, 我们称之为降级幂集, 它更接近传统集合论中的幂集. `ℙ[_]` 与 `ℙ` 的区别在于, `ℙ` 的迭代会不断提高宇宙层级, 而 `ℙ[_]` 的迭代全都发生在一开始固定下来的层级.

```agda
ℙ[_] : (𝓋 : Level) → Type 𝓊 → Type (𝓊 ⊔ 𝓋 ⁺)
ℙ[ 𝓋 ] X = X → hProp 𝓋
```

与迭代幂集 `ℙ[_]⁺` 类似地. 我们有固定宇宙的迭代降级幂集 `ℙ[_][_]⁺`.

```agda
ℙ[_][_]⁺ : (𝓋 : Level) → ℕ → Type 𝓊 → Type (𝓊 ⊔ 𝓋 ⁺)
ℙ[ 𝓋 ][ zero ]⁺  X = ℙ[ 𝓋 ] X
ℙ[ 𝓋 ][ suc n ]⁺ X = ℙ[ 𝓋 ][ n ]⁺ X → hProp 𝓋
```

现在, 局部假设 `PR`, 我们来处理两种幂集的联系.

```agda
module _ ⦃ _ : PR ⦄ where
```

如果有 `X → Y` 的函数, 那么 `X` 的降级幂集 `A` 可以转化为 `Y` 的降级幂集, 只需对任意 `y : Y` 取 `∀ x → f x ≡ y → ⟨ A x ⟩`.

注意这两个降级幂集的等级与 `X` 和 `Y` 的等级这四个等级之间都可以没有必然联系, 或者说在非直谓设定下它们其实都是同一级, 但形式上我们不得不采用一般化的形式.

```agda
  Morphℙ : (X → Y) → ℙ[ 𝓊 ] X → ℙ[ 𝓋 ] Y
  Morphℙ f A y = Resize $ (∀ x → f x ≡ y → ⟨ A x ⟩) , isPropΠ2 λ _ _ → str (A _)
```

迭代该函数, 就可以将n迭代幂集转化为n迭代降级幂集.

```agda
  Resizeℙⁿ : (n : ℕ) → ℙ[ n ]⁺ X → ℙ[ 𝓊 ][ n ]⁺ X
  Resizeℙⁿ zero = Morphℙ (idfun _)
  Resizeℙⁿ (suc n) = Morphℙ (Resizeℙⁿ n)
```

**引理** 给定单射 `f : X → Y`, 那么 `Morphℙ f` 也是单射.  
**证明** 假设 `p q : ℙ[ 𝓊 ] X` 满足 `eq : Morphℙ f p ≡ Morphℙ f q`, 要证 `p ≡ q`. 由于幂集是一个函数, 由函数外延性只需证对任意 `x` 有 `p x ≡ q x`. 此时等号两边是命题, 由命题外延性只需证 `⟨ p x ⟩ ↔ ⟨ q x ⟩`.

```agda
  Morphℙ-inj : (f : X → Y) → injective f → injective (Morphℙ {𝓊 = 𝓊} {𝓋} f)
  Morphℙ-inj f f-inj {p} {q} eq = funExt λ x → hPropExt $
```

左边到右边, 假设有 `⟨ p x ⟩`, 要证 `⟨ q x ⟩`. 由 `f` 的单射性有 `∀ y → f y ≡ f x → ⟨ p y ⟩`, 此即 `⟨ Morphℙ f p (f x) ⟩`.

用 `eq` 改写它得 `⟨ Morphℙ f q (f x) ⟩`, 即 `∀ y → f y ≡ f x → ⟨ q y ⟩`. 输入 `x` 和 `refl` 即得 `⟨ q x ⟩`.

```agda
      →: (λ px → let
          H₁ : ⟨ Morphℙ f p (f x) ⟩
          H₁ = resize λ y fy≡fx → subst (λ - → ⟨ p - ⟩) (sym $ f-inj fy≡fx) px
          H₂ : ⟨ Morphℙ f q (f x) ⟩
          H₂ = subst (λ - → ⟨ - (f x) ⟩) eq H₁
        in unresize H₂ x refl)
```

同理可证右边到左边. ∎

```agda
      ←: (λ px → let
          H₁ : ⟨ Morphℙ f q (f x) ⟩
          H₁ = resize λ y fy≡fx → subst (λ - → ⟨ q - ⟩) (sym $ f-inj fy≡fx) px
          H₂ : ⟨ Morphℙ f p (f x) ⟩
          H₂ = subst (λ - → ⟨ - (f x) ⟩) (sym eq) H₁
        in unresize H₂ x refl)
```

由以上引理, 幂集到降级幂集的转化都是单射.

```agda
  Resizeℙⁿ-inj : (n : ℕ) → injective (Resizeℙⁿ {X = X} {𝓊} n)
  Resizeℙⁿ-inj zero = Morphℙ-inj (idfun _) (idfun _)
  Resizeℙⁿ-inj (suc n) = Morphℙ-inj (Resizeℙⁿ n) (Resizeℙⁿ-inj n)
```

## 非构造性公理

本文研究的非构造性公理包括排中律, 选择公理, 连续统假设和广义连续统假设.

### 排中律

我们说一个类型 `A` 可判定, 记作 `Dec A`, 当且仅当 `A` 成立或者 `A` 的否定成立.

`Dec` 与和类型有类似的结构, 它的构造子有两个, `yes` 和 `no`. `yes` 的参数是 `A` 的证明, `no` 的参数是 `¬ A` 的证明. 引理 `isPropDec` 说明 `Dec` 是一个谓词.

```agda
open import Cubical.Relation.Nullary public
  using (NonEmpty; Dec; yes; no; isPropDec)
```

排中律即是说任意命题都是可判定的.

```agda
LEM : (𝓊 : Level) → Type _
LEM 𝓊 = (P : Type 𝓊) → isProp P → Dec P
```

排中律本身是一个命题, 因为可判定性是一个谓词.

```agda
isPropLEM : (𝓊 : Level) → isProp (LEM 𝓊)
isPropLEM 𝓊 = isPropΠ2 λ _ → isPropDec
```

虽然我们不能证明排中律, 但我们可以证明对任意类型, 它的可判定性非空 (双重否定成立). 这在有些书上也叫做排中律不可辩驳.

```agda
NonEmptyDec : (A : Type 𝓊) → NonEmpty (Dec A)
NonEmptyDec _ ¬dec = ¬dec $ no λ a → ¬dec $ yes a
```

### 选择公理

选择公理是说对于任意集合 `A` 和 `B` 以及它们之间的命题关系 `R`, 如果对任意 `x : A` 都存在一个 `y : B` 使得 `R x y` 成立, 那么存在一个函数 `f : A → B` 使得对任意 `x : A` 有 `R x (f x)` 成立.

```agda
AC : (𝓊 𝓋 𝓌 : Level) → Type _
AC 𝓊 𝓋 𝓌 = (A : Type 𝓊) (B : Type 𝓋) (R : A → B → Type 𝓌) →
  isSet A → isSet B → (∀ x y → isProp (R x y)) →
  (∀ x → ∃ y ∶ B , R x y) → ∃ f ∶ (A → B) , ∀ x → R x (f x)
```

选择公理也是一个命题, 因为其表述是一个嵌套Π类型, 其目标是Σ类型的命题截断.

```agda
isPropAC : (𝓊 𝓋 𝓌 : Level) → isProp (AC 𝓊 𝓋 𝓌)
isPropAC 𝓊 𝓋 𝓌 = isPropΠ6 λ _ _ _ _ _ _ → isPropΠ λ _ → squash₁
```

### 连续统假设

连续统假设是说如果有单射链 `ℕ ↪ X ↪ ℙ ℕ` 且 `¬ X ↪ ℕ`, 那么 `ℙ ℕ ≲ X`, 也就是说没有一个集合在势的意义上正好卡在自然数集及其幂集之间.

```agda
isCHType : Type 𝓊 → Type 𝓋 → Type _
isCHType N X = N ↪ X → (¬ X ↪ N) → X ↪ ℙ N → ℙ N ≲ X

CH : (𝓊 : Level) → Type _
CH 𝓊 = (X : Type 𝓊) → isSet X → isCHType ℕ X
```

注意 `CH` 表述中嵌套Π类型的最终目标使用了命题截断, 这保证了 `CH` 是一个命题.

```agda
isPropCH : (𝓊 : Level) → isProp (CH 𝓊)
isPropCH 𝓊 = isPropΠ5 λ _ _ _ _ _ → squash₁
```

### 广义连续统假设

无穷集定义为被自然数集单射的集合.

```agda
infinite : Type 𝓊 → Type _
infinite X = ℕ ↪ X
```

广义连续统假设是说, 对任意无穷集和它的幂集, 都没有一个集合在势的意义上正好卡在它们中间.

```agda
isGCHType : Type 𝓊 → Type 𝓋 → Type _
isGCHType X Y = infinite X → X ↪ Y → Y ↪ ℙ X → Y ≲ X ⊎ ℙ X ≲ Y

GCH : (𝓊 𝓋 : Level) → Type _
GCH 𝓊 𝓋 = (X : Type 𝓊) (Y : Type 𝓋) → isSet X → isSet Y → isGCHType X Y
```

注意 `GCH` 最终指向的和类型并没有做命题截断, 但我们仍然能证明 `GCH` 是一个命题. 实际上, 只要和类型的两边是互斥的命题, 那么这个和类型就是命题. 不难看出 `Y ↪ X` 与 `ℙ X ↪ Y` 互斥, 否则违反康托尔定理, 所以广义连续统假设也是一个命题. 我们把相关证明放在下一章.

广义连续统假设蕴含连续统假设.

```agda
GCH→CH : ∀ 𝓊 → GCH 𝓊₀ 𝓊 → CH 𝓊
GCH→CH 𝓊 gch X X-set ℕ↪X ¬X↪ℕ X↪ℙℕ with gch ℕ X isSetℕ X-set ↪-refl ℕ↪X X↪ℙℕ
... | (⊎.inl X↪ℕ)  = ∥∥₁-map (⊥-rec ∘ ¬X↪ℕ) X↪ℕ
... | (⊎.inr ℙℕ↪X) = ℙℕ↪X
```
