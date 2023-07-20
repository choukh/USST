---
title: 泛等结构集合论 (2) 开胃菜:CH → LEM
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
zhihu-url: https://zhuanlan.zhihu.com/p/643217740
---

# 泛等结构集合论 (2) 开胃菜: CH → LEM

> 交流Q群: 893531731  
> 本文源码: [CH→LEM.lagda.md](https://github.com/choukh/USST/blob/main/src/ReverseMath/CH→LEM.lagda.md)  
> 高亮渲染: [CH→LEM.html](https://choukh.github.io/USST/ReverseMath.CH→LEM.html)  

我们导入前置知识, 并全局假设 `PR`. 我们来证明在直觉主义中连续统假设蕴含排中律.

```agda
{-# OPTIONS --cubical --safe #-}
open import Preliminary
module ReverseMath.CH→LEM ⦃ _ : PR ⦄ where
```

## 康托尔定理

首先我们复刻质料集合论的基本结果: 康托尔定理. 它可以在直觉主义中证明.

**定理** 任意类型都不能被自己的幂集单射.

```agda
Cantor-≴ : (X : Type 𝓊) → ℙ X ≴ X
```

**证明** 用归谬法, 假设有 `ℙ X` 到 `X` 的单射函数 `f`, 要推出矛盾. 证明思路跟集合论中的一样. 我们用对角线法构造一个集合 `A : ℙ X`, 使得 `f A ∈ A` 当且仅当 `f A ∉ A`, 从而违反无矛盾律.

```agda
Cantor-≴ X (f , f-inj) = noncontradiction ∈→∉ ∉→∈
  where
```

这个对角线集 `A` 是这么一个集合, 对于它里面的任意 `x`, 只要这个 `x` 等于某个 `f B`, 那么 `x` 就不在这个 `B` 里面. 这句话形式化为一个Π类型, 它最终指向空类型, 而空类型是命题, 所以这个Π类型也是命题, 从而这句话良好地定义了 `X` 的一个子集.

注意这个Π类型 (全称量化) 提升了宇宙等级, 它比 `X` 高一个宇宙, 我们要用 `PR` 把它压下来. 可能可以使用宇宙多态的 `ℙ` 使得子集可以位于不同的宇宙, 从而不需要 `PR` 也应该可以证明康托尔定理. 但这会增加整个形式化的复杂度, 而且后续章节有必须使用 `PR` 的地方, 所以我们就干脆全局假设了 `PR`.

```agda
  A : ℙ X
  A x = Resize $ (∀ B → f B ＝ x → x ∉ B) , isPropΠ3 λ _ _ _ → isProp⊥
```

一旦对角线集 `A` 构造完成, 由定义立即有 `f A ∈ A` 蕴含 `f A ∉ A`.

```agda
  ∈→∉ : f A ∈ A → f A ∉ A
  ∈→∉ fA∈A = unresize fA∈A A refl
```

另一方面, 假设 `f A ∉ A`, 要证 `f A ∈ A`. 即假设有一个 `B` 满足 `f B ＝ f A`, 要证 `f A ∉ B`. 由 `f` 的单射性可知 `A ＝ B`, 用它改写前提 `f A ∉ A` 右边的 `A` 即证. ∎

```agda
  ∉→∈ : f A ∉ A → f A ∈ A
  ∉→∈ fA∉A = resize λ B fB＝ → transport (f A ∉_) (f-inj (sym fB＝)) fA∉A
```

由康托尔定理我们可以知道作为 `GCH` 结论的那个和类型的两边互斥, 从而证明 `GCH` 的命题性. 今后不需要用到这一结论.

```agda
isPropGCH : (𝓊 𝓋 : Level) → isProp (GCH 𝓊 𝓋)
isPropGCH 𝓊 𝓋 = isPropΠ4 λ X Y _ _ → isPropΠ3 λ _ _ _ →
  λ { (⊎.inl _)    (⊎.inl _)    → eqToPath $ ap ⊎.inl $ squash₁Eq _ _
    ; (⊎.inl Y≲X)  (⊎.inr ℙX≲Y) → ⊥-rec $ ∥∥-rec2 isProp⊥ (λ ℙX≲Y Y≲X → Cantor-≴ _ $ ≲-trans Y≲X ℙX≲Y) Y≲X ℙX≲Y
    ; (⊎.inr ℙX≲Y) (⊎.inl Y≲X)  → ⊥-rec $ ∥∥-rec2 isProp⊥ (λ ℙX≲Y Y≲X → Cantor-≴ _ $ ≲-trans Y≲X ℙX≲Y) Y≲X ℙX≲Y
    ; (⊎.inr _)    (⊎.inr _)    → eqToPath $ ap ⊎.inr $ squash₁Eq _ _ }
```

## 单集

现在固定一个集合 `X`.

```agda
module Lemmas (X : Type 𝓊) (X-set : isSet X) where
```

由 `X` 的某个项 `x` 所构成的单集 `｛ x ｝ : ℙ X` 定义为谓词 `x ＝_`. `X` 的集合性保证了 `x ＝_` 是一个谓词.

```agda
  opaque
    ｛_｝ : X → ℙ X
    ｛ x ｝ y = (x ＝ y) , transportIsProp (X-set _ _)
```

由 `_＝_` 的基本性质可以证明单集构造 `｛_｝` 具有单射性.

```agda
    ｛｝-inj : injective ｛_｝
    ｛｝-inj H = transport (idfun _) (sym $ ap fst $ happly H _) refl
```

我们说一个 `A : ℙ X` 是单集, 当且仅当它等于某个 `｛ x ｝`.

```agda
  is｛｝ : ℙ X → Type _
  is｛｝ A = Σ x ∶ X , A ＝ ｛ x ｝
```

注意尽管这里用的是Σ类型, 我们仍然能证明 "是单集" 是一个谓词, 因为见证 `A` 是单集的那个 `x` 唯一. 不过后面不需要用到这一结论.

```agda
  isPropIs｛｝ : (A : ℙ X) → isProp (is｛｝ A)
  isPropIs｛｝ A (x₁ , refl) (x₂ , eq) = eqToPath $ Σ≡Prop
    (λ _ → isPropPathToIsProp $ transportIsProp $ isSetΠ (λ _ → isSetHProp) _ _)
    (｛｝-inj eq)
```

接着我们证明康托尔定理的一个变体, 说 `ℙ X` 的自嵌入一定射到了单集之外. 我们能实际构造出这个非单集, 用的还是对角线法, 证明的结构与 `Cantor-≴` 非常类似, 这里不再赘述.

```agda
  Cantor-beyond｛｝ : (f : ℙ X → ℙ X) → injective f → Σ A ∶ ℙ X , ¬ is｛｝ (f A)
  Cantor-beyond｛｝ f f-inj = A , λ (x , fA＝) → noncontradiction (∈→∉ x fA＝) (∉→∈ x fA＝)
    where
    A : ℙ X
    A x = Resize $ (∀ B → f B ＝ ｛ x ｝ → x ∉ B) , isPropΠ3 λ _ _ _ → isProp⊥
    ∈→∉ : ∀ x → (f A ＝ ｛ x ｝) → x ∈ A → x ∉ A
    ∈→∉ x fA＝ x∈A = unresize x∈A A fA＝
    ∉→∈ : ∀ x → (f A ＝ ｛ x ｝) → x ∉ A → x ∈ A
    ∉→∈ x fA＝ x∉A = resize λ B fB＝ → transport (x ∉_) (f-inj (fA＝ ∙ sym fB＝)) x∉A
```

## 关键构造

现在, 在之前固定的集合 `X` 的基础上再固定一个类型 `P`. 这个 `P` 将对应于排中律所谈论的那个 `P`.

```agda
  module _ (P : Type 𝓋) where
```

接下来是一个关键构造. 我们构造类型 `Y`, 使得其项是 `X` 的满足以下**任一**条件的子集.

- 是单集
- `P` 可判定

```agda
    Y : Type (𝓊 ⁺ ⊔ 𝓋)
    Y = Σ A ∶ ℙ X , (is｛｝ A ∨ Dec P)
```

首先, 不难证明, `Y` 是一个集合. 因为它作为一个Σ类型, 左边是 `A` 的子集, 右边是一个谓词.

```agda
    isSetY : isSet Y
    isSetY = isSetΣ isSetℙ λ _ → isProp→isSet squash₁
```

接下来是3个显然的事实.

1. `X` 单射到 `Y`, 只需将 `x` 映射到 `｛ x ｝` 即可.

```agda
    X≲Y : X ≲ Y
    X≲Y = (λ x → ｛ x ｝ , inl (x , refl)) , ｛｝-inj ∘ (ap fst)
```

2. `Y` 单射到 `ℙ X`, 因为 `Y` 的项都是 `X` 的满足某些条件的子集.

```agda
    Y≲ℙX : Y ≲ ℙ X
    Y≲ℙX = fst , λ fst-eq → Σ≡Prop (λ _ → squash₁Eq) fst-eq
```

3. 如果 `P` 可判定, 那么 `ℙ X` 单射到 `Y`, 因为这时 `X` 的所有子集都满足 `P` 可判定, 都会包括在 `Y` 里面.

```agda
    dec→ℙX≲Y : Dec P → ℙ X ≲ Y
    dec→ℙX≲Y P-dec = (λ A → A , inr P-dec) , ap fst
```

**引理** 如果 `P` 是命题且 `ℙ X` 单射到 `Y`, 那么 `P` 可判定.  
**证明** 给定 `ℙ X` 到 `Y` 的单射 `f`, 这样 `fst ∘ f` 则是 `ℙ X` 到 `ℙ X` 的单射. 由康托尔定理的变体 `Cantor-beyond｛｝`, 我们可以拿到一个 `A : ℙ X` 满足 `f A : Y` 非单集, 那么由 `Y` 的定义, 只能有 `P` 可判定. ∎

```agda
    ℙX≲Y→dec : isProp P → ℙ X ≲ Y → Dec P
    ℙX≲Y→dec P-prop ℙX≲Y with ℙX≲Y
    ... | (f , f-inj) with Cantor-beyond｛｝ (fst ∘ f) (f-inj ∘ (Σ≡Prop λ _ → squash₁Eq))
    ... | (A , ¬sing) with f A
    ... | (fA , sing∨dec) = ∥∥-rec (isPropDec P-prop)
      (λ { (⊎.inl sing) → ⊥-rec $ ¬sing sing
         ; (⊎.inr dec)  → dec })
      sing∨dec
```

这说明了当 `P` 是命题的时候, `Dec P` 与 `ℙ X ≲ Y` 逻辑等价. 因为 `P` 是任意给定的, 那么只要证明了用这个 `P` 构造的 `Y` 满足 `ℙ X ≲ Y`, 就证明了排中律.

此外, 由于 `X` 也是任意给定的, 我们令 `X = ℕ`, 那么 `ℙ ℕ ≲ Y` 正是 `CH` 所承诺的结论, 只要有 `X ≲ Y`, `Y ≴ X` 以及 `Y ≲ ℙ X`. 第一个和第三个在上面已证, 我们只差 `Y ≴ X`. 这是核心一步.

## 核心步骤

我们用上一条引理, 结合康托尔定理, 证明 `Y` 不能单射到 `X`.

**引理** `Y` 不能单射到 `X`.  
**证明** 用归谬法, 假设 `Y ≲ X`, 要推出矛盾. 由前置知识我们知道 `P` 的可判定性不可辩驳, 那么我们只要证明 `P` 不可判定就能得到矛盾. 再用归谬法, 假设 `P` 可判定, 要推出矛盾. 这时我们有前提 "`P` 可判定" 且 `Y ≲ X`. 由上一条引理, `P` 可判定意味着 `ℙ X ≲ Y`. 又 `Y ≲ X`, 由 `≲` 的传递性有 `P X ≲ X`, 与康托尔定理矛盾. ∎

```agda
    Y≴X : Y ≴ X
    Y≴X Y≲X@(f , f-inj) = NonEmptyDec P λ P-dec → Cantor-≴ X (≲-trans (dec→ℙX≲Y P-dec) Y≲X)
```

有了这个引理, 接下来的两条引理就是自明的了. 只是要注意命题截断的一些技术细节. `CH` 将给我们 `≲` 的命题截断, 由于最终目标 `Dec P` 也是命题, 可以用 `∥∥-rec` 消掉这个截断.

```agda
    isCHType→ℙX≲Y : isCHType X Y → ∥ ℙ X ≲ Y ∥₁
    isCHType→ℙX≲Y ch-type = ch-type (X≲Y , Y≴X) Y≲ℙX

    isCHType→lem : isCHType X Y → isProp P → Dec P
    isCHType→lem ch-type P-prop = ∥∥-rec (isPropDec P-prop) (ℙX≲Y→dec P-prop) (isCHType→ℙX≲Y ch-type)
```

## 结论

**定理** 如果 `CH` 在任意宇宙成立, 那么 `LEM` 在任意宇宙成立.  
**证明** 要证任意命题 `P` 可判定. 令 `Y` 为满足以下**任一**条件的自然数子集所组成的集合:

- 是单集
- `P` 可判定

由前几小节的讨论可知 `Y` 满足 `CH` 的前提 `ℕ ⋨ Y ≲ ℙ ℕ`, 于是可以得到 `CH` 所承诺的 `ℙ ℕ` 到 `Y` 的单射. 但是由康托尔定理的一个变体, `ℙ ℕ` 必然要单射到非单集的子集, 所以 `Y` 并不只有单集, 所以只能有 `P` 可判定. ∎

```agda
CH→LEM : (∀ 𝓊 → CH 𝓊) → (∀ 𝓊 → LEM 𝓊)
CH→LEM ch 𝓊 P = isCHType→lem _ $ ch _ _ $ isSetY _
  where open Lemmas ℕ isSetℕ
```
