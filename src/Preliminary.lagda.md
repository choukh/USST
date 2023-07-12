---
title: 泛等结构集合论 (1) 前置知识
zhihu-tags: Agda, 数理逻辑, 集合论
zhihu-url: https://zhuanlan.zhihu.com/p/643059692
---

# 泛等结构集合论 (1) 前置知识

> 交流Q群: 893531731  
> 本文源码: [Preliminary.lagda.md](https://github.com/choukh/USST/blob/main/src/Preliminary.lagda.md)  
> 高亮渲染: [Preliminary.html](https://choukh.github.io/USST/Preliminary.html)  

## 前言

**泛等基础 (univalent foundations, 简称 UF)** 中有原生的集合概念 `hSet`, 它可以视作一种**结构集合论 (structural set theory)** 的模型. 我们尝试在其中复刻传统质料集合论 (material set theory) 的基本概念, 如势, 序数, 连续统假设 (CH), 广义连续统假设 (GCH) 等, 并研究它们与排中律 (LEM) 和选择公理 (AC) 之间的反推事实. 这得益于 UF 是一种**中性数学基础 (foundation of neutral constructive mathematics)**. 本文是这一系列的第一篇, 主要介绍前置知识, 包括泛等基础以及集合论的一些基本概念.

所谓泛等基础, 简单来说就是在 Martin-Löf 类型论 (MTLL) 的基础上加上泛等公理 (UA) 所得到的扩展, 它解决了 MLTT 的一些问题, 从而足够作为一种数学基础. 本文中我们使用 [Cubical Agda](https://agda.readthedocs.io/en/v2.6.3/language/cubical.html) 来作为泛等基础的具体实现.

```agda
{-# OPTIONS --cubical --safe #-}
module Preliminary where
```

## 泛等基础

### 判断

我们从比较集合论基础的异同开始讲起. 类似于在集合论中可以谈论的任意 $x$ 都是集合那样, 在类型论中可以谈论的任意 $x$ 都具有一个类型. 我们不能在集合论中谈论 $x$ 是不是集合, 我们也不能在类型论中谈论 $x$ 是不是具有某一类型 $A$. 像这种在理论中不能谈论的元命题我们叫做一个**判断 (judgement)**. 相比集合论, 在类型论中需要更常接触各种判断, 所以有必要澄清这个概念.

我们将 " $x$ 具有类型 $A$" 记作 $x : A$, $x$ 又叫做 $A$ 的项. 科普介绍中经常把 $x : A$ 解释成 $x ∈ A$, 虽然在一些情况下不妨这么理解, 但它们本质上是不同层面的概念. 与 $x : A$ 同一个层面的是 "x是集合" 这一判断, 而 $∈$ 只是集合上配备的一种二元关系. 类似地, 类型 A 上也可以配备上某种二元关系 $∼$.

### 命题即类型

正如集合论中的 $x ∈ y$ 构成了一个命题那样, 类型论中给定 $x\,y : A$, 那么 $x ∼ y$ 也构成了一个命题. 实际上, 类型论中的每个命题也都是一个类型. 如果能构造出该类型的一个项, 我们就认为证明了该类型所对应的那个命题. 注意, 尽管命题都是类型, 但并非所有类型都是命题. 关于这一点将在后面的同伦层级这一小节解释. 如果把一个类型 $A$ 看作命题, 那个 $A$ 的项 $x : A$ 也叫 $A$ 的一个证明或证据; 如果可以构造 $x : A$, 我们就说 $A$ 可证或 $A$ 成立.

|         |  集合论      | 类型论
| ----    |  ----       | ----
| 判断     | x 是集合    | x : A
| 不能谈论  | x 是不是集合 | x 是不是具有某类型 A
| 命题     | x ∈ y       | x ∼ y : Type

### 类型宇宙与宇宙层级

正如 $x : A$ 是一个判断那样, " $A$ 是一个类型" 也是一个判断, 记作 `A : Type`. 其中 `Type` 就叫做**类型宇宙 (type universe)**. 它是一个层级系统, 其层级序数叫做宇宙层级 `Level`. 但要注意 `Level` 本身不在类型宇宙之中, 它独享一个单独的宇宙, 叫做层级宇宙 `LevelUniv`, 即有 `Level : LevelUniv`. (这些不同的宇宙又叫做 sort, 非形式地, 我们可以说 `Type : Sort` 和 `LevelUniv : Sort`)

最低的宇宙层级是 `ℓ-zero : Level`, 位于最低宇宙层级的类型记作 `Type ℓ-zero`, 简记作 `Type`. 下一个宇宙是 `Type (ℓ-suc ℓ-zero)`, 简记作 `Type₁`, 以此类推. 此外, 宇宙层级还有一个二元运算 `_⊔_`, 它的作用是取两个宇宙层级中较高的那一个, 例如 `ℓ-zero ⊔ (ℓ-suc ℓ-zero)` 等于 `ℓ-suc ℓ-zero`.

以上都是类型论中的原始概念, 我们从 `Cubical.Core.Primitives` 模块中通过以下代码导入了它们.

```agda
open import Cubical.Core.Primitives public
  using (Type; Level; ℓ-zero; ℓ-suc)
  renaming (ℓ-max to _⊔_)
```

我们约定在系列文章中都使用 `ℓ` 和 `ℓ′` 表示宇宙层级参数. 例如 `A : Type ℓ` 表示任意给定的宇宙层级 `ℓ` 的类型 `A`.

```agda
variable ℓ ℓ′ : Level
```

关于宇宙层级的作用我们在接下来的几小节穿插讲解.

### 函数类型

如质料集合论中的原始概念 $∈$ 那样, 类型论中的 $→$ 也是一个原始概念. 它是一个**类型形成子 (type former)**, 给定 `A : Type ℓ` 和 `B : Type ℓ′`, 那么 `A → B` 是一个新的类型, 它就是 $A$ 到 $B$ 的**函数类型 (function type)**. 注意 `A → B` 位于宇宙 `Type (ℓ ⊔ ℓ′)` 之中, 因为 `A → B` 要位于 `A` 和 `B` 所位于的宇宙的较大者之中.

函数类型的项具有 lambda 表达式的形式. 例如恒等函数 $f : A → A$ 定义为 $f ≔ λx.x$. 在 Agda 中定义符号 ≔ 就写作普通等号 =, 分隔绑定变量与表达式的点号 $.$ 写作 $→$, 所以上式在代码中写作 `f = λ x → x`. 我们今后只采用这一种写法. 注意不要跟作为类型形成子的 `→` 混淆.

扩展函数类型的概念, 我们有类型宇宙上的函数类型, 如 `Type ℓ → Type ℓ′`. 尝试理解以下代码, 这是 Agda 中定义新的项的最常用写法, 先写项的类型判断, 再换一行写这个项的定义. 其中 `_` 表示我们定义的是一个匿名项, 它无法被引用, 举例子的时候经常用到这种写法.

```agda
_ : Type ℓ → Type ℓ′ → Type (ℓ ⊔ ℓ′)
_ = λ A B → A → B
```

最后面的 `Type (ℓ ⊔ ℓ′)` 可以简写作 `Type _`, 因为 Agda 可以推断出 `A → B` 必须位于 `ℓ ⊔ ℓ′` 宇宙.

```agda
_ : Type ℓ → Type ℓ′ → Type _
_ = λ A B → A → B
```

### 类型族

我们继续扩展函数类型的概念. 给定 `A : Type ℓ`, 那么 `A → Type ℓ′` 就叫做以 `A` 为**索引 (index)**的**类型族 (family of type)**. 我们知道命题也是类型, 那么类型族的一个简单的例子是关于 `A` 的谓词, 它就具有 `A → Type ℓ′` 的类型. 给定关于 `A` 的谓词 `B : A → Type ℓ′` 以及一个 `a : A`, 那么 `B a` 就表示 "`a` 满足 `B`" 这一命题. 注意这里写的 `B a` 是一个函数应用, 在 Agda 中没有歧义的情况下函数应用不需要加括号, 我们也遵循这一惯例.

类型族 `A → Type ℓ′` 位于类型宇宙 `Type (ℓ ⊔ ℓ-suc ℓ′)` 之中. 这是因为类型宇宙 `Type ℓ′` 本身位于下一个宇宙 `Type (ℓ-suc ℓ′)` 之中, 而 `A → Type ℓ′` 要位于 `A` 和 `Type ℓ′` 所位于的宇宙的较大者之中.

```agda
_ : Type ℓ → (ℓ′ : Level) → Type (ℓ ⊔ ℓ-suc ℓ′)
_ = λ A ℓ′ → A → Type ℓ′
```

### 依值函数类型 (Π类型)

我们继续扩展函数类型的概念. 给定 `A : Type ℓ` 和 `B : A → Type ℓ′`, 那么 `(x : A) → B x` 叫做**依值函数类型 (dependent function type)**, 也叫做**Π类型 (Pi type)**. 它是函数类型 `A → B` 的依值版本, 可以看到它们具有类似的形式. Π类型在非形式的文献里一般写作 $\Pi_{x : A} B(x)$, 在 Agda 中还可以写作 `∀ x → B x` 或者 `∀ (x : A) → B x`. 采用"命题即类型"的解读, Π类型可以简单理解为是全称量化命题所具有的类型.

Π类型 `∀ x → B x` 位于类型宇宙 `Type (ℓ ⊔ ℓ′)`, 这与函数类型 `A → B` 的情况是一样的.

```agda
_ : (A : Type ℓ) → (A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
_ = λ A B → ∀ x → B x
```

我们导入 `Cubical` 库中关于函数的相关概念, 包括函数的应用 `_$_`, 函数的复合 `_∘_`, 恒等函数 `idfun`. 使用 `_$_` 可以少写一些括号, 例如 `f (g x)` 可以写作 `f $ g x`. 使用 `_∘_` 可以少写一些 lambda 表达式, 例如 `λ x → f (g x)` 可以写作 `f ∘ g`. `_$_` 和 `_∘_` 都适用于依值函数.

```agda
open import Cubical.Foundations.Function public
  using (_$_; _∘_; idfun)
```

### 依值配对类型 (Σ类型)

**依值配对类型 (dependent pair type)**, 也叫做**Σ类型 (Sigma type)**, 可以看作是Π类型的反柯里化. 也就是说, 以下两个类型是等价的.

`∀ x → B x → C`

`(Σ A B) → C`

逻辑上可以解读为, "对任意 `x`, 如果 `B x` 成立, 那么 `C` 成立" 等价于 "如果存在 `x`, 使得 `B x` 成立,那么 `C` 成立". 但要注意我们后面会对逻辑上的存在量词有更加精确的刻画, 它并不完全对应于Σ类型. 我们有时会把 `Σ A B` 读作 "`A` 配备上结构 `B`".

库中的 `Σ-syntax` 提供了Σ类型 `Σ A B` 另一种写法 `Σ[ x ∈ A ] B x`, 方便做变量绑定. **积类型 (product type)** `A × B` 定义为 `Σ A (λ _ → B)`, 这是Σ类型的非依值版本, 对应于笛卡尔积. 不论是依值配对还是非依值配对, 我们都可以用 `fst` 取得配对的左边, `snd` 取得配对的右边.

```agda
open import Cubical.Data.Sigma public
  using (Σ; Σ-syntax; _×_; _,_; fst; snd)
```

Σ类型 `Σ A B` 位于类型宇宙 `Type (ℓ ⊔ ℓ′)` 之中, 这与Π类型的情况是一样的.

```agda
_ : (A : Type ℓ) → (A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
_ = λ A B → Σ A B
```

### 基本数据类型

上面讲的类型都是从已有的类型构造新的类型, 而本小节将介绍具体的类型.

空类型 `⊥ : Type` 是其项无法被构造的类型, 对应于逻辑假, 正如假无法被证明. `⊥-rec` 是爆炸律, 即我们可以通过证明假来证明任何命题.

```agda
open import Cubical.Data.Empty public
  using (⊥) renaming (rec to ⊥-rec)
```

命题 `A` 的否定是 `A` 到 `⊥` 的函数 `A → ⊥`, 简记作 `¬ A`.

```agda
open import Cubical.Relation.Nullary public using (¬_)
```

单元类型 `Unit : Type` 对应于逻辑真, 它只有一个项 `tt : Unit`. 本文不需要用到.

自然数类型由以下两条规则归纳定义而成.

    --------
    zero : ℕ

    m : ℕ
    ---------
    suc m : ℕ

```agda
open import Cubical.Data.Nat public using (ℕ)
```

至此我们快速回顾了 MLTT 的一些基本概念, 接下来将介绍泛等基础所特有的概念.

### 同伦层级

如果说宇宙层级是类型宇宙 `Type ℓ` 所具有的一种属性, 那么同伦层级 (hLevel) 则是类型 `A : Type ℓ` 所具有的一种属性. 更具体的解释可以参考同伦类型论 (homotopy type theory, 简称 HoTT) 的相关资料, 本文中我们只关心同伦层级为 1 和 2 的两种类型.

同伦层级为 1 的类型叫做命题, 该类类型的任意项都可证相等. "类型 `A` 是命题" 表达为 `isProp A`. 如所期待的那样, 类型 `isProp A` 也是一个命题, 即对任意 `A : Type ℓ` 可证 `isProp (isProp A)`. 我们也说 `isProp` 是一个谓词.

同伦层级为 2 的类型叫做集合, 该类类型的任意两个项的相等都是命题, 即给定两个项相等的任意两个证明, 这两个证明是相等的. "类型 `A` 是集合" 表达为 `isSet A`. 与 `isProp` 一样, `isSet` 也是一个谓词. 此外我们有 `isProp→isSet`, 即任意命题都是集合. 直观上, 由于命题的任意项都相等, 那么这些项之间的相等的方式也应该是相等的, 所以命题也是集合.

```agda
open import Cubical.Foundations.Prelude public
  using (isProp; isSet; isProp→isSet)
```

可以证明空类型是命题, 自然数类型是集合.

```agda
open import Cubical.Data.Empty public using (isProp⊥)
open import Cubical.Data.Nat public using (isSetℕ)
```

对于嵌套的Π类型, 不管嵌套多少次, 只要最后的目标是命题 (或集合), 那么整个嵌套Π类型也是命题 (或集合). 如果构成Σ类型的两边都是命题 (或集合), 那么这个Σ类型也是命题 (或集合).

```agda
open import Cubical.Foundations.HLevels public
  using ( isPropΠ; isPropΠ2; isPropΠ3; isPropΠ4; isPropΠ5; isPropΠ6
        ; isSetΠ; isSetΣ)
```

命题宇宙 `hProp ℓ` 定义为 `Type ℓ` 配备上结构 `isProp`, 即 `hProp ℓ = Σ (Type ℓ) isProp`. 引理 `isSetHProp` 告诉我们, 命题宇宙 `hProp ℓ` 是集合.

```agda
open import Cubical.Foundations.HLevels public using (hProp; isSetHProp)
```

类似地, 集合宇宙 `hSet ℓ` 定义为 `Type ℓ` 配备上结构 `isSet`, 即 `hSet ℓ = Σ (Type ℓ) isSet`. 但本文中不直接使用 `hSet`. 为了方便处理, 我们会尽可能地使用它们的柯里化版本, 即说 "给定类型 `A`, 如果它是命题 (或集合), 那么怎么怎么样", 而不说 "给定命题 (或集合) `A`, 怎么怎么样".

我们把具有某种结构的类型宇宙叫做 `TypeWithStr`, 并用 `⟨_⟩` 取得其左边的类型, 用 `str` 取得其右边的结构. 例如对于 `A : hProp ℓ`, `⟨ A ⟩` 是一个类型, `str A` 是 "`⟨ A ⟩` 是命题" 的证据.

```agda
open import Cubical.Foundations.Structure public
  using (⟨_⟩; str)
```

### 命题截断

命题截断 `∥_∥₁` 用于把一个可能不是命题的类型转化为命题. `∣_∣₁` 用于构造命题截断的项, `squash₁` 用于证明命题截断后的类型的项确实都是相等的.

```agda
open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁; squash₁)
```

我们有引理 `∥∥-rec`, 它说如果目标 `P` 是命题, 那么我们可以通过证明 `A → P` 来证明 `∥ A ∥₁ → P`.  
我们有引理 `∥∥-map`, 它说可以通过证明 `A → B` 来证明 `∥ A ∥₁ → ∥ B ∥₁`.  
我们有引理 `∥∥-map2`, 它说可以通过证明 `A → B → C` 来证明 `∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁`.

```agda
  renaming (rec to ∥∥-rec; map to ∥∥-map; map2 to ∥∥-map2)
```

Σ类型的命题截断完全对应了逻辑上的存在量化命题.

```agda
open import Cubical.Data.Sigma public using (∃; ∃-syntax)
```

### 相等类型

"相等" 在泛等基础中是一个复杂的概念. 首先上面提到的库中的概念所涉及到的相等都采用了所谓**路径类型 (path type)**. 但本文中将使用定义为**归纳类型族 (inductive type family)** 的**命题相等类型 (propositional equality)**, 也就是下面导入的 `_≡_`. 两种相等类型的定义是等价的, 但后者在非同伦论的数学中更加直观, 也更加容易使用. 我们导入了一堆它们之间的相互转化引理: `eqToPath`, `pathToEq`, `Path≡Eq` 等, 以灵活处理各种情况. 使用 `Σ≡Prop` 可以通过证明两个依值配对的左边分别相等来证明这两个依值配对相等, 只要它们的右边是一个谓词.

`_≡_` 具有自反性 `refl`, 对称性 `sym` 和 传递性 `_∙_`. 其中 `refl` 是 `_≡_` 归纳类型的唯一构造子, 可以做模式匹配和反演推理. 实际上, 包括对称性和传递性在内的 `_≡_` 的其他性质都通过 `refl` 推导而来.

`ap` 也叫合同性, 它说 `x ≡ y → f x ≡ f y`.  
`happly` 也叫做同伦应用, 它说 `f ≡ g → (x : A) → f x ≡ g x`.  
`transport` 也叫做等量替换, 它说 `x ≡ y → P x → P y`.

```agda
open import Cubical.Data.Equality public
  using ( _≡_; refl; sym; _∙_; ap; happly; transport
        ; eqToPath; pathToEq; Path≡Eq; isPropPathToIsProp; Σ≡Prop)
  renaming (squash₁ to squash₁Eq)
```

以下引理会经常用到, 它将 "路径类型是命题" 的证明转化成 "相等类型是命题" 的证明.

```agda
open import Agda.Builtin.Cubical.Path public renaming (_≡_ to Path)

transportIsProp : {A : Type ℓ} {x y : A} → isProp (Path x y) → isProp (x ≡ y)
transportIsProp = transport isProp Path≡Eq
```

### 幂集

给定任意类型 `X : Type ℓ`, 我们把 `X` 到命题宇宙 `hProp ℓ` 的函数叫做 `X` 的幂集, 记作 `ℙ X`, 它的项也叫 `X` 的子集.

给定项 `x : X` 和子集 `A : ℙ X`, "`x` 属于 `A`" 定义为 `⟨ A x ⟩`. `A` 是取值到 `hProp ℓ` 的函数, 这保证了属于关系是取值到命题的. 此外, 可以证明幂集确实是一个集合: `isSetℙ`.

```agda
open import Cubical.Foundations.Powerset public
  using (ℙ; _∈_; isSetℙ)
```

不属于符号 `_∉_` 定义为 `_∈_` 的否定, 即 `x ∉ A = ¬ x ∈ A`.

```agda
_∉_ : {X : Type ℓ} → X → ℙ X → Type _
x ∉ A = ¬ x ∈ A
```

## 公理

本文需要假设一个公理, 即**命题宇宙调整 (propositional resizing, 简称PR)**. PR的宣告实际上等于是取消了命题宇宙的分层, 使得它只有一层, 所有命题都位于那一层.

如果取消所有类型的分层, 那么将导致罗素悖论, 而只取消命题宇宙的分层则不会. 我们只会进入所谓**非直谓 (impredicative)** 的数学世界, 而经典数学都是这样的.

代码工程上, 我们使用了 record 类型, 它可以视作一种带了很多语法糖的Σ类型. 我们定义的 `PropositionalResizing` 包括了一个 `Resize` 函数, 以实现给定的两个命题宇宙的相互转换, 并且它需要满足 `resize` 和 `unresize` 性质, 即转换前后的两个命题逻辑等价.

```agda
record PropositionalResizing (ℓ ℓ′ : Level) : Type (ℓ-suc ℓ ⊔ ℓ-suc ℓ′) where
  field
    Resize : hProp ℓ → hProp ℓ′
    resize : {P : hProp ℓ} → ⟨ P ⟩ → ⟨ Resize P ⟩
    unresize : {P : hProp ℓ} → ⟨ Resize P ⟩ → ⟨ P ⟩
```

以下代码是 Agda 的一些小技巧, 不熟悉 Agda 可以不看. 只需知道我们只要在模块声明中以 `⦃ _ : PR ⦄` 的形式声明参数, 那么就等于假设了 PR, 就可以在该模块中尽情地使用上面的三个函数, 而不用显式说明具体是哪两个命题宇宙之间的转换.

```agda
PR = ∀ {ℓ ℓ′} → PropositionalResizing ℓ ℓ′

module _ ⦃ pr : PropositionalResizing ℓ ℓ′ ⦄ where
  open PropositionalResizing pr public
```

## 命题逻辑

本小节我们来补齐泛等基础中对应于直觉主义命题逻辑的相关概念. 我们约定仅在本文剩下的篇幅中使用 `A` `B` `C` 表示任意层级的类型.

```agda
private variable A B C : Type ℓ
```

以下是无矛盾律在直觉主义中更容易处理的版本. 因为我们无法证明排中律 "`A` 或 `¬ A`", 所以单有 `A → ¬ A → ⊥` 也无法推出矛盾, 必须采用下面的形式才行.

```agda
noncontradiction : (A → ¬ A) → (¬ A → A) → ⊥
noncontradiction p q = p (q λ a → p a a) (q λ a → p a a)
```

逻辑析取定义为**和类型 (sum type)** 的命题截断. 因为和类型的项起码有两种 (左边或右边) 不同的构造方式, 但析取不关心具体是哪种, 所以必须要做命题截断, 以确保所有证明项都相等.

```agda
open import Cubical.Data.Sum as ⊎ public using (_⊎_)

infixr 2 _∨_
_∨_ : Type ℓ → Type ℓ′ → Type _
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

## 排中律

我们说一个类型 `A` 可判定, 记作 `Dec A`, 当且仅当 `A` 成立或者 `A` 的否定成立.

`Dec` 与和类型有类似的结构, 它的构造子有两个, `yes` 和 `no`. `yes` 的参数是 `A` 的证明, `no` 的参数是 `¬ A` 的证明. 引理 `isPropDec` 说明 `Dec` 是一个谓词.

```agda
open import Cubical.Relation.Nullary public
  using (NonEmpty; Dec; yes; no; isPropDec)
```

排中律即是说任意命题都是可判定的.

```agda
LEM : (ℓ : Level) → Type _
LEM ℓ = (P : Type ℓ) → isProp P → Dec P
```

排中律本身是一个命题, 因为可判定性是一个谓词.

```agda
isPropLEM : (ℓ : Level) → isProp (LEM ℓ)
isPropLEM ℓ = isPropΠ2 λ _ → isPropDec
```

虽然我们不能证明排中律, 但我们可以证明对任意类型, 它的可判定性非空 (双重否定成立). 这在有些书上也叫做排中律不可辩驳.

```agda
DecNonEmpty : (A : Type ℓ) → NonEmpty (Dec A)
DecNonEmpty _ ¬dec = ¬dec $ no λ a → ¬dec $ yes a
```

## 选择公理

选择公理是说对于任意集合 `A` 和 `B` 以及它们之间的命题关系 `R`, 如果对任意 `x : A` 都存在一个 `y : B` 使得 `R x y` 成立, 那么存在一个函数 `f : A → B` 使得对任意 `x : A` 有 `R x (f x)` 成立.

```agda
AC : (ℓ ℓ′ ℓ′′ : Level) → Type _
AC ℓ ℓ′ ℓ′′ = (A : Type ℓ) (B : Type ℓ′) (R : A → B → Type ℓ′′) →
  isSet A → isSet B → (∀ x y → isProp (R x y)) →
  (∀ x → ∃[ y ∈ B ] R x y) → ∃[ f ∈ (A → B) ] ∀ x → R x (f x)
```

选择公理也是一个命题, 因为其表述是一个嵌套Π类型, 其目标是Σ类型的命题截断.

```agda
isPropAC : (ℓ ℓ′ ℓ′′ : Level) → isProp (AC ℓ ℓ′ ℓ′′)
isPropAC ℓ ℓ′ ℓ′′ = isPropΠ6 λ _ _ _ _ _ _ → isPropΠ λ _ → squash₁
```

## 势

我们说类型 `A` 的势小于等于 `B`, 当且仅当有任意 `A` 到 `B` 的单射函数. 注意这里用的是Σ类型, 我们并没有做命题截断. 有时候延迟截断会更方便处理.

```agda
injective : (A → B) → Type _
injective f = ∀ {x y} → f x ≡ f y → x ≡ y

_≤_ : Type ℓ → Type ℓ′ → Type _
A ≤ B = Σ (A → B) injective

_≰_ : Type ℓ → Type ℓ′ → Type _
A ≰ B = ¬ A ≤ B
```

`≤` 构成一个预序.

```agda
≤-refl : A ≤ A
≤-refl = idfun _ , λ refl → refl

≤-trans : A ≤ B → B ≤ C → A ≤ C
≤-trans (f , f-inj) (g , g-inj) = g ∘ f , f-inj ∘ g-inj
```

`≤` 的反对称性 (即施罗德-伯恩斯坦定理) 依赖于排中律.

我们说 `A` 的势严格小于 `B`, 当且仅当 `A` 的势小于等于 `B` 且 `B` 的势不小于等于 `A`.

```agda
_<_ : Type ℓ → Type ℓ′ → Type _
A < B = A ≤ B × B ≰ A
```

## 连续统假设

连续统假设是说如果一个集合的势严格大于自然数集, 并且小于等于自然数集的幂集, 那么它的势就大于等于自然数集的幂集. 由于没有排中律, 我们采用了这种迂回表达.

```agda
isCHType : Type ℓ → Type ℓ′ → Type _
isCHType X Y = X < Y → Y ≤ ℙ X → ∥ ℙ X ≤ Y ∥₁

CH : (ℓ : Level) → Type _
CH ℓ = (X : Type ℓ) → isSet X → isCHType ℕ X
```

注意 `CH` 表述中嵌套Π类型的最终目标使用了命题截断, 这保证了 `CH` 是一个命题.

```agda
isPropCH : (ℓ : Level) → isProp (CH ℓ)
isPropCH ℓ = isPropΠ4 λ _ _ _ _ → squash₁
```

## 广义连续统假设

无穷集定义为势大于等于自然数集的集合.

```agda
infinite : Type ℓ → Type _
infinite X = ℕ ≤ X
```

广义连续统假设是说, 对任意无穷集和它的幂集, 都没有一个正好卡在它们中间的势.

```agda
isGCHType : Type ℓ → Type ℓ′ → Type _
isGCHType X Y = infinite X → X ≤ Y → Y ≤ ℙ X → Y ≤ X ∨ ℙ X ≤ Y

GCH : (ℓ ℓ′ : Level) → Type _
GCH ℓ ℓ′ = (X : Type ℓ) (Y : Type ℓ′) → isSet X → isSet Y → isGCHType X Y
```

同样地, 广义连续统假设也是一个命题.

```agda
isPropGCH : (ℓ ℓ′ : Level) → isProp (GCH ℓ ℓ′)
isPropGCH ℓ ℓ′ = isPropΠ4 λ _ _ _ _ → isPropΠ3 λ _ _ _ → squash₁
```

广义连续统假设蕴含连续统假设.

```agda
GCH→CH : ∀ ℓ → GCH ℓ-zero ℓ → CH ℓ
GCH→CH ℓ gch X X-set (ℕ≤X , X≰ℕ) X≤ℙℕ =
  ∥∥-map (λ { (⊎.inl X≤ℕ)  → ⊥-rec $ X≰ℕ X≤ℕ
            ; (⊎.inr ℙℕ≤X) → ℙℕ≤X })
  $ gch ℕ X isSetℕ X-set ≤-refl ℕ≤X X≤ℙℕ
```
