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

满射 `surjective` 的定义与传统的一致. `isEmbedding×isSurjection→isEquiv` 说明一个函数是同伦嵌入且满射, 那么它是同伦等价.

```agda
open import Cubical.Functions.Surjection public
  renaming (isSurjection to surjective) using (isEmbedding×isSurjection→isEquiv)
```

可以证明, 如果一个单射是射到集合的, 那么它是同伦嵌入.

```agda
open import Cubical.Functions.Embedding using (hasPropFibers→isEmbedding)

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

## 公理

本文研究的公理包括降级公理, 排中律, 选择公理, 连续统假设和广义连续统假设.

### 降级公理

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
