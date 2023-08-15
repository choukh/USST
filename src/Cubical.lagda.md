---
title: 泛等结构集合论 (1) 泛等基础
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
zhihu-url: https://zhuanlan.zhihu.com/p/643059692
---

# 泛等结构集合论 (1) 泛等基础

> 交流Q群: 893531731  
> 本文源码: [Cubical.lagda.md](https://github.com/choukh/USST/blob/main/src/Cubical.lagda.md)  
> 高亮渲染: [Cubical.html](https://choukh.github.io/USST/Cubical.html)  

## 前言

**泛等基础 (univalent foundations, 简称 UF)** 中有原生的集合概念 `hSet`, 叫做**同伦集 (homotopy-sets)**. 我们决定尽量避免提到同伦的概念, 所以这里叫它**泛等结构集 (univalent structural sets)**, 由于它是一种**结构集合论 (structural set theory)**. 我们尝试在其中复刻传统质料集合论 (material set theory) 的基本概念, 如序数, 基数, 连续统假设 (CH), 广义连续统假设 (GCH) 等, 并研究它们与排中律 (LEM) 和选择公理 (AC) 之间的反推事实. 这得益于 UF 是一种**中性数学基础 (foundation of neutral constructive mathematics)**. 本文是这一系列的第一篇, 主要介绍泛等基础的一些基本概念.

所谓泛等基础, 简单来说就是在 Martin-Löf 类型论 (MLTT) 的基础上加上泛等公理 (UA) 所得到的扩展, 它解决了 MLTT 的一些问题, 从而足够作为一种数学基础. 本文中我们使用 [Cubical Agda](https://agda.readthedocs.io/en/v2.6.3/language/cubical.html) 立方类型论来作为泛等基础的具体实现.

```agda
{-# OPTIONS --cubical --safe #-}
module Cubical where
```

## 判断

我们从比较集合论基础的异同开始讲起. 类似于在集合论中可以谈论的任意 $x$ 都是集合那样, 在类型论中可以谈论的任意 $x$ 都具有一个类型. 我们不能在集合论中谈论 $x$ 是不是集合, 我们也不能在类型论中谈论 $x$ 是不是具有某一类型 $A$. 像这种在理论中不能谈论的元命题我们叫做一个**判断 (judgement)**. 相比集合论, 在类型论中需要更常接触各种判断, 所以有必要澄清这个概念.

我们将 " $x$ 具有类型 $A$" 记作 $x : A$, $x$ 又叫做 $A$ 的项. 科普介绍中经常把 $x : A$ 解释成 $x ∈ A$, 虽然在一些情况下不妨这么理解, 但它们本质上是不同层面的概念. 与 $x : A$ 同一个层面的是 "x是集合" 这一判断, 而 $∈$ 只是集合上配备的一种二元关系. 类似地, 类型 A 上也可以配备上某种二元关系 $∼$.

## 命题即类型

正如集合论中的 $x ∈ y$ 构成了一个命题那样, 类型论中给定 $x\,y : A$, 那么 $x ∼ y$ 也构成了一个命题. 实际上, 类型论中的每个命题也都是一个类型. 如果能构造出该类型的一个项, 我们就认为证明了该类型所对应的那个命题. 注意, 尽管命题都是类型, 但并非所有类型都是命题. 关于这一点将在后面的同伦层级这一小节解释. 如果把一个类型 $A$ 看作命题, 那个 $A$ 的项 $x : A$ 也叫 $A$ 的一个证明或证据; 如果可以构造 $x : A$, 我们就说 $A$ 可证或 $A$ 成立.

|         |  集合论      | 类型论
| ----    |  ----       | ----
| 判断     | x 是集合    | x : A
| 不能谈论  | x 是不是集合 | x 是不是具有某类型 A
| 命题     | x ∈ y       | x ∼ y : Type

## 类型宇宙与宇宙层级

正如 $x : A$ 是一个判断那样, " $A$ 是一个类型" 也是一个判断, 记作 `A : Type`. 其中 `Type` 就叫做**类型宇宙 (type universe)**. 它是一个层级系统, 其层级序数叫做宇宙层级 `Level`. 但要注意 `Level` 本身不在类型宇宙之中, 它独享一个单独的宇宙, 叫做层级宇宙 `LevelUniv`, 即有 `Level : LevelUniv`. (这些不同的宇宙又叫做 sort, 非形式地, 可以认为 `Type₀ : Type₁ : Type₂ : ... : Sort` 和 `LevelUniv : Sort`)

最低的宇宙层级是 `𝓊₀ : Level`, 位于最低层级的类型宇宙记作 `Type 𝓊₀`, 简记作 `Type₀` 或 `Type`. 下一个宇宙是 `Type (𝓊₀ ⁺)`, 简记作 `Type 𝓊₁`, 或 `Type₁`, 以此类推. 此外, 宇宙层级还有一个二元运算 `_⊔_`, 它的作用是取两个宇宙层级中较高的那一个, 例如 `𝓊₀ ⊔ 𝓊₁` 等于 `𝓊₁`. 较低层级的类型可以被 `Lift` 提升到较高层级.

以上都是类型论中的原始概念, 我们从 `Cubical.Core.Primitives` 模块中通过以下代码导入了它们.

```agda
open import Cubical.Foundations.Prelude public
  using (Type; Level; Lift)
  renaming (ℓ-zero to 𝓊₀; ℓ-suc to _⁺; ℓ-max to _⊔_)

𝓊₁ = 𝓊₀ ⁺
𝓊₂ = 𝓊₁ ⁺
```

我们约定在系列文章中都使用 `𝓊`, `𝓋`, `𝓌` 等表示宇宙层级参数. 例如 `A : Type 𝓊` 表示任意给定的宇宙层级 `𝓊` 的类型 `A`.

```agda
variable 𝓊 𝓋 𝓌 𝓊′ 𝓋′ 𝓌′ : Level
```

关于宇宙层级的作用我们在接下来的几小节穿插讲解.

## 函数类型

如质料集合论中的原始概念 $∈$ 那样, 类型论中的 $→$ 也是一个原始概念. 它是一个**类型形成子 (type former)**, 给定 `A : Type 𝓊` 和 `B : Type 𝓋`, 那么 `A → B` 是一个新的类型, 它就是 $A$ 到 $B$ 的**函数类型 (function type)**. 注意 `A → B` 位于宇宙 `Type (𝓊 ⊔ 𝓋)` 之中, 因为 `A → B` 要位于 `A` 和 `B` 所位于的宇宙的较大者之中.

函数类型的项具有 lambda 表达式的形式. 例如恒等函数 $f : A → A$ 定义为 $f ≔ λx.x$. 在 Agda 中定义符号 ≔ 就写作普通等号 =, 分隔绑定变量与表达式的点号 $.$ 写作 $→$, 所以上式在代码中写作 `f = λ x → x`. 我们今后只采用这一种写法. 注意不要跟作为类型形成子的 `→` 混淆.

扩展函数类型的概念, 我们有类型宇宙上的函数类型, 如 `Type 𝓊 → Type 𝓋`. 尝试理解以下代码, 这是 Agda 中定义新的项的最常用写法, 先写项的类型判断, 再换一行写这个项的定义. 其中 `_` 表示我们定义的是一个匿名项, 它无法被引用, 举例子的时候经常用到这种写法.

```agda
_ : Type 𝓊 → Type 𝓋 → Type (𝓊 ⊔ 𝓋)
_ = λ A B → A → B
```

最后面的 `Type (𝓊 ⊔ 𝓋)` 可以简写作 `Type _`, 因为 Agda 可以推断出 `A → B` 必须位于 `𝓊 ⊔ 𝓋` 宇宙.

```agda
_ : Type 𝓊 → Type 𝓋 → Type _
_ = λ A B → A → B
```

## 类型族

我们继续扩展函数类型的概念. 给定 `A : Type 𝓊`, 那么 `A → Type 𝓋` 就叫做以 `A` 为**索引 (index)**的**类型族 (family of type)**. 我们知道命题也是类型, 那么类型族的一个简单的例子是关于 `A` 的谓词, 它就具有 `A → Type 𝓋` 的类型. 给定关于 `A` 的谓词 `B : A → Type 𝓋` 以及一个 `a : A`, 那么 `B a` 就表示 "`a` 满足 `B`" 这一命题. 注意这里写的 `B a` 是一个函数应用, 在 Agda 中没有歧义的情况下函数应用不需要加括号, 我们也遵循这一惯例.

类型族 `A → Type 𝓋` 位于类型宇宙 `Type (𝓊 ⊔ 𝓋 ⁺)` 之中. 这是因为类型宇宙 `Type 𝓋` 本身位于下一个宇宙 `Type (𝓋 ⁺)` 之中, 而 `A → Type 𝓋` 要位于 `A` 和 `Type 𝓋` 所位于的宇宙的较大者之中.

```agda
_ : Type 𝓊 → (𝓋 : Level) → Type (𝓊 ⊔ 𝓋 ⁺)
_ = λ A 𝓋 → A → Type 𝓋
```

## 依值函数类型 (Π类型)

我们继续扩展函数类型的概念. 给定 `A : Type 𝓊` 和 `B : A → Type 𝓋`, 那么 `(x : A) → B x` 叫做**依值函数类型 (dependent function type)**, 也叫做**Π类型 (Pi type)**. 它是函数类型 `A → B` 的依值版本, 可以看到它们具有类似的形式. Π类型在非形式的文献里一般写作 $\Pi_{x : A} B(x)$, 在 Agda 中还可以写作 `∀ x → B x` 或者 `∀ (x : A) → B x`. 采用"命题即类型"的解读, Π类型可以简单理解为是全称量化命题所具有的类型.

Π类型 `∀ x → B x` 位于类型宇宙 `Type (𝓊 ⊔ 𝓋)`, 这与函数类型 `A → B` 的情况是一样的.

```agda
_ : (A : Type 𝓊) → (A → Type 𝓋) → Type (𝓊 ⊔ 𝓋)
_ = λ A B → ∀ x → B x
```

我们导入 `Cubical` 库中关于函数的相关概念, 包括函数的应用 `_$_`, 函数的复合 `_∘_`, 恒等函数 `idfun`. 使用 `_$_` 可以少写一些括号, 例如 `f (g x)` 可以写作 `f $ g x`. 使用 `_∘_` 可以少写一些 lambda 表达式, 例如 `λ x → f (g x)` 可以写作 `f ∘ g`. `_$_` 和 `_∘_` 都适用于依值函数.

```agda
open import Cubical.Foundations.Function public
  using (_$_; _∘_; idfun; flip; curry; uncurry)
open import Function public using (_∘₂_)
```

## 依值配对类型 (Σ类型)

**依值配对类型 (dependent pair type)**, 也叫做**Σ类型 (Sigma type)**, 可以看作是Π类型的反柯里化 `uncurry`. 也就是说, 以下两个类型是等价的.

`∀ x → B x → C`

`(Σ A B) → C`

逻辑上可以解读为, "对任意 `x`, 如果 `B x` 成立, 那么 `C` 成立" 等价于 "如果存在 `x`, 使得 `B x` 成立,那么 `C` 成立". 但要注意我们后面会对逻辑上的存在量词有更加精确的刻画, 它并不完全对应于Σ类型. 我们有时会把 `Σ A B` 读作 "`A` 配备上结构 `B`".

**积类型 (product type)** `A × B` 定义为 `Σ A (λ _ → B)`, 这是Σ类型的非依值版本, 对应于笛卡尔积. 不论是依值配对还是非依值配对, 我们都可以用 `fst` 取得配对的左边, `snd` 取得配对的右边.

```agda
open import Cubical.Data.Sigma public
  using (Σ; _,_; fst; snd) renaming (_×_ to infixr 3 _×_)
```

我们定义Σ类型 `Σ A B` 另一种写法 `Σ x ∶ A , B x`, 方便做变量绑定.

```agda
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ x ∶ A , B
```

Σ类型 `Σ A B` 位于类型宇宙 `Type (𝓊 ⊔ 𝓋)` 之中, 这与Π类型的情况是一样的.

```agda
_ : (A : Type 𝓊) → (A → Type 𝓋) → Type (𝓊 ⊔ 𝓋)
_ = λ A B → Σ A B
```

## 基本数据类型

上面讲的类型都是从已有的类型构造新的类型, 而本小节将介绍具体的类型.

空类型 `⊥ : Type` 是其项无法被构造的类型, 对应于逻辑假, 正如假无法被证明. `⊥-rec` 是爆炸律, 即我们可以通过证明假来证明任何命题.

```agda
open import Cubical.Data.Empty public
  using (⊥; ⊥*) renaming (rec to ⊥-rec)
```

命题 `A` 的否定是 `A` 到 `⊥` 的函数 `A → ⊥`, 简记作 `¬ A`.

```agda
open import Cubical.Relation.Nullary public using (¬_)
```

单元类型 `⊤ : Type` 对应于逻辑真, 它只有一个项 `tt : Unit`.

```agda
open import Cubical.Data.Unit public
  using (tt; tt*) renaming (Unit to ⊤; Unit* to ⊤*)
```

自然数类型由以下两条规则归纳定义而成.

    --------
    zero : ℕ

    m : ℕ
    ---------
    suc m : ℕ

```agda
open import Cubical.Data.Nat public using (ℕ; zero; suc)
```

至此我们快速回顾了 MLTT 的一些基本概念, 接下来将介绍泛等基础所特有的概念.

## 同伦层级

如果说宇宙层级是类型宇宙 `Type 𝓊` 所具有的一种属性, 那么同伦层级 (hLevel) 则是类型 `A : Type 𝓊` 所具有的一种属性. 更具体的解释可以参考同伦类型论 (homotopy type theory, 简称 HoTT) 的相关资料, 本文中我们只关心同伦层级为 1 和 2 的两种类型.

同伦层级为 1 的类型叫做命题, 该类类型的任意项都可证相等. "类型 `A` 是命题" 表达为 `isProp A`. 如所期待的那样, 类型 `isProp A` 也是一个命题, 即对任意 `A : Type 𝓊` 可证 `isProp (isProp A)`. 我们也说 `isProp` 是一个谓词.

同伦层级为 2 的类型叫做集合, 该类类型的任意两个项的相等都是命题, 即给定两个项相等的任意两个证明, 这两个证明是相等的. "类型 `A` 是集合" 表达为 `isSet A`. 与 `isProp` 一样, `isSet` 也是一个谓词. 此外我们有 `isProp→isSet`, 即任意命题都是集合. 直观上, 由于命题的任意项都相等, 那么这些项之间的相等的方式也应该是相等的, 所以命题也是集合.

```agda
open import Cubical.Foundations.Prelude public
  using (isProp; isSet; isPropIsProp; isProp→isSet)
```

可以证明空类型, 单元类型和自然数类型都是集合.

```agda
open import Cubical.Data.Empty public using (isProp⊥; isProp⊥*)
open import Cubical.Data.Unit public renaming (isPropUnit to isProp⊤; isPropUnit* to isProp⊤*)
open import Cubical.Data.Nat public using (isSetℕ)
```

对于嵌套的Π类型, 不管嵌套多少次, 只要最后的目标是命题 (或集合), 那么整个嵌套Π类型也是命题 (或集合). 如果构成Σ类型的两边都是命题 (或集合), 那么这个Σ类型也是命题 (或集合). 引理 `isOfHLevelLift` 是说宇宙层级的提升不影响同伦层级.

```agda
open import Cubical.Foundations.HLevels public
  using ( isPropΠ; isPropΠ2; isPropΠ3; isPropΠ4; isPropΠ5; isPropΠ6; isProp→
        ; isProp×; isProp×2; isProp×3; isProp×4; isProp×5; isPropΣ
        ; isSetΠ; isSetΠ2; isSetΠ3; isSetΣ; isOfHLevelLift)
```

命题宇宙 `hProp 𝓊` 定义为 `Type 𝓊` 配备上结构 `isProp`, 即 `hProp 𝓊 = Σ (Type 𝓊) isProp`. 出乎意料的是, 命题宇宙 `hProp 𝓊` 也是一个集合. 在传统基础中所有命题不可能组成集合, 因为太大了. 但泛等基础中说的集合不关乎大小, 大小已经由宇宙层级处理了.

```agda
open import Cubical.Foundations.HLevels public using (hProp; isSetHProp)
```

类似地, 集合宇宙 `hSet 𝓊` 定义为 `Type 𝓊` 配备上结构 `isSet`, 即 `hSet 𝓊 = Σ (Type 𝓊) isSet`. 但本文中一般不直接使用 `hSet`. 为了方便处理, 我们会尽可能地使用它们的柯里化版本, 即说 "给定类型 `A`, 如果它是命题 (或集合), 那么怎么怎么样", 而不说 "给定命题 (或集合) `A`, 怎么怎么样". 需要注意的是, 集合宇宙 `hSet 𝓊` 本身不是集合, 而是一个群胚.

```agda
open import Cubical.Foundations.HLevels public using (hSet; isGroupoidHSet)
```

我们把具有某种结构的类型宇宙叫做 `TypeWithStr`, 并用 `⟨_⟩` 取得其左边的类型, 用 `str` 取得其右边的结构. 例如对于 `A : hProp 𝓊`, `⟨ A ⟩` 是一个类型, `str A` 是 "`⟨ A ⟩` 是命题" 的证据.

```agda
open import Cubical.Foundations.Structure public
  using (TypeWithStr; ⟨_⟩; str)
```

## 命题截断

命题截断 `∥_∥₁` 用于把一个可能不是命题的类型转化为命题. `∣_∣₁` 用于构造命题截断的项, `squash₁` 用于证明命题截断后的类型的项确实都是相等的.

```agda
open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁; squash₁)
```

我们有引理 `∥∥₁-rec`, 它说如果目标 `P` 是命题, 那么我们可以通过证明 `A → P` 来证明 `∥ A ∥₁ → P`.  
我们有引理 `∥∥₁-rec2`, 它说如果目标 `P` 是命题, 那么我们可以通过证明 `A → B → P` 来证明 `∥ A ∥₁ → ∥ B ∥₁ → P`.  
我们有引理 `∥∥₁-map`, 它说可以通过证明 `A → B` 来证明 `∥ A ∥₁ → ∥ B ∥₁`.  
我们有引理 `∥∥₁-map2`, 它说可以通过证明 `A → B → C` 来证明 `∥ A ∥₁ → ∥ B ∥₁ → ∥ C ∥₁`.  
最后, 我们有 `∥∥₁-elim` 和 `∥∥₁-elim2`, 分别是 `∥∥₁-rec` 和 `∥∥₁-rec2` 的依值版本.

```agda
  renaming ( rec to ∥∥₁-rec; rec2 to ∥∥₁-rec2; rec3 to ∥∥₁-rec3
           ; map to ∥∥₁-map; map2 to ∥∥₁-map2
           ; elim to ∥∥₁-elim; elim2 to ∥∥₁-elim2; elim3 to ∥∥₁-elim3)
```

Σ类型的命题截断完全对应了逻辑上的存在量化命题.

```agda
open import Cubical.Data.Sigma public using (∃)

∃-syntax = ∃
infix 2 ∃-syntax
syntax ∃-syntax A (λ x → B) = ∃ x ∶ A , B
```

## 集合截断

与命题截断类似的, 我们有集合截断 `∥_∥₂`, 它将高阶群胚截断为集合.

```agda
open import Cubical.HITs.SetTruncation public
  using (∥_∥₂; ∣_∣₂; squash₂)
  renaming ( rec to ∥∥₂-rec; rec2 to ∥∥₂-rec2; map to ∥∥₂-map
           ; elim to ∥∥₂-elim; elim2 to ∥∥₂-elim2; elim3 to ∥∥₂-elim3)
```

## 相等类型

"相等" 在泛等基础中是一个复杂的概念. 我们采用所谓**道路类型 (path type)** `PathP` 来表示相等. 它是一种异质相等, 其同质版记作 `_≡_`. 这里不会讲解它们的底层原理, 只简单介绍一下基本性质.

```agda
open import Cubical.Foundations.Prelude public
  using ( PathP; _≡_; step-≡; _≡⟨⟩_; _∎
        ; refl; sym; _∙_; cong; cong₂; subst; subst2
        ; transport; funExt; funExt⁻; isProp→PathP)
```

- 首先最基本地, `_≡_` 具有自反性 `refl`, 对称性 `sym` 和 传递性 `_∙_`.
- `step-≡` `_≡⟨⟩_` `_∎` 是一些方便的记号, 允许我们写等式推导链, 本质上是传递性.
- `cong` 叫做合同性.
  - 库里的定义是相当一般化的版本, 除去里面涉及的依赖类型和异质相等, 简单来说合同性说的是 `x ≡ y → f x ≡ f y`.
  - `cong₂` 是双参数版本的合同性, 简单来说是 `x ≡ y → u ≡ v → f x u ≡ f y v`.
- `subst` 就是等量替换: `x ≡ y → P x → P y`.
  - `subst2` 是双参数版本的等量替换: `x ≡ y → u ≡ v → P x u → P y v`.
- `transport` 允许两个类型之间的等量替换: `A ≡ B → A → B`.
- `funExt` 是函数的外延性: `(∀ x → f x ≡ g x) → f ≡ g`.
- `funExt⁻` 是函数的外延性的逆: `f ≡ g → (∀ x → f x ≡ g x)`.
- `isProp→PathP` 用于证明两个谓词应用的相等.
  - 因为谓词是一个依赖函数, 在证明它所依赖的项相等之前, 谓词应用的相等看起来就是一个异质相等, 所以需要用 `PathP` 表达.

`ΣPathP` 用于证明两个Σ类型相等, 通过证明它们的左右两边分别相等.

```agda
open import Cubical.Data.Sigma public using (ΣPathP)
```

由于经常出现Σ类型的右边是命题的情况, 我们专门写出以下引理方便处理.

```agda
Σ≡Prop : {A : Type 𝓊} {B : A → Type 𝓋} → (∀ x → isProp (B x)) →
  {p q : Σ A B} → fst p ≡ fst q → p ≡ q
Σ≡Prop {B} prop path = ΣPathP (path , isProp→PathP (λ i → prop _) _ _)
```

## 同伦等价

同伦等价 `_≃_` 可以简单理解为是在泛等基础中更容易处理的一种"同构", 它与真正的同构 `Iso` 也是同构的, 且同伦等价的. 同伦等价是一个Σ类型, 其左边即同伦等价的底层函数, 它与同构的正映射相同. 同伦等价相比于同构的好处之一是"一个函数是一个同伦等价"一定是一个命题 (`isPropIsEquiv`), 而同构则不一定有这种性质. 由此性质我们有 `equivEq`, 它说如果底层函数道路相等, 那么同伦等价也道路相等.

此外, `idEquiv` 是同伦等价的自反性; `invEquiv` 是同伦等价的对称性; `compEquiv` 是同伦等价的传递性; `cong≃` 是同伦等价的合同性; `LiftEquiv` 说明宇宙层级的提升不影响同伦等价.

```agda
open import Cubical.Foundations.Equiv public
  using ( _≃_; isEquiv; isPropIsEquiv
        ; idEquiv; invEquiv; compEquiv; LiftEquiv
        ; equivEq; secIsEq; retIsEq; equivToIso)
open import Cubical.Foundations.Equiv.Properties public using (cong≃)
open import Cubical.Foundations.Isomorphism public using (Iso; iso; section; retract; isoToEquiv)
```

为了方便阅读我们分别用 `_⁺¹` 和 `_⁻¹` 表示同伦等价所承诺的正映射和逆映射. `secIsEq` 以及 `retIsEq` 说它们互逆.

```agda
_⁺¹ : {A : Type 𝓊} {B : Type 𝓋} → A ≃ B → A → B
_⁺¹ = fst

_⁻¹ : {A : Type 𝓊} {B : Type 𝓋} → A ≃ B → B → A
e ⁻¹ = fst (invEquiv e)
```

## 泛等原理

在 Cubical 中泛等公理 `ua` 是一个定理, 我们今后称之为泛等原理. 它说两个类型如果等价, 那么相等, 即对任意 `A` 和 `B` 有 `A ≃ B → A ≡ B`. 我们几乎不需要直接使用 `ua`, 更多地是用它的推论, 已经在上面分散地给出.

```agda
open import Cubical.Foundations.Univalence public using (ua)
```

以下是用 Agda 反射机制定义的宏, 搭配同伦等价使用, 用于更快地证明一些数学结构的**泛等原理 (univalence principle)**. 我们不需要关心这些工具的实现细节, 只需要知道什么是结构的泛等原理, 以及如何使用这套工具得到它. 具体可以看 `𝒮ᴰ-Record` 定义下面的例子, 以及本系列讲义的后续文章.

```agda
open import Cubical.Displayed.Base public using (DUARel; UARel; ∫)
open import Cubical.Displayed.Auto public using (autoDUARel)
open import Cubical.Displayed.Record public using (𝒮ᴰ-Record; fields:; _data[_∣_∣_]; _prop[_∣_])
open import Cubical.Displayed.Universe public using (𝒮-Univ)
```

为了编程上的方便, 我们经常需要用 Agda 的反射机制将Σ类型与 record 类型相互转化.

```agda
open import Cubical.Reflection.RecordEquiv public using (declareRecordIsoΣ)
```

再用 `isOfHLevelRetractFromIso` 将对 record 类型的命题/集合性的证明转化为对与之同构的Σ类型的命题/集合性的证明.

```agda
open import Cubical.Foundations.HLevels public using (isOfHLevelRetractFromIso)
```
