---
title: 泛等结构集合论 (2) CH → LEM
zhihu-tags: Agda, 数理逻辑, 集合论
---

# 泛等结构集合论 (2) CH → LEM

> 交流Q群: 893531731  
> 本文源码: [CH→LEM.lagda.md](https://github.com/choukh/USST/blob/main/src/CH→LEM.lagda.md)  
> 高亮渲染: [CH→LEM.html](https://choukh.github.io/USST/CH→LEM.html)  

我们导入前置知识, 并全局假设 `PR`. 我们来证明在直觉主义中连续统假设蕴含排中律.

```agda
{-# OPTIONS --cubical --safe #-}
open import Preliminary
module CH→LEM ⦃ _ : PR ⦄ where
```

## 康托尔定理

首先我们复刻集合论的基本结果: 康托尔定理. 它可以在直觉主义中证明.

**定理** 对任意类型 `X` 有 `ℙ X ≰ X`.

```agda
Cantor-≰ : (X : Type ℓ) → ℙ X ≰ X
```

**证明** 用归谬法, 即假设有 `ℙ X` 到 `X` 的单射函数 `f`, 要推出矛盾. 证明思路跟集合论中的一样. 我们用对角线法构造一个集合 `A : ℙ X`, 使得 `f A ∈ A` 当且仅当 `f A ∉ A`, 从而违反无矛盾律.

```agda
Cantor-≰ X (f , f-inj) = noncontradiction ∈→∉ ∉→∈
  where
```

这个对角线集 `A` 是这么一个集合, 对于它里面的任意 `x`, 只要这个 `x` 等于某个 `f B`, 那么 `x` 就不在这个 `B` 里面. 这句话形式化为一个Π类型, 它最终指向空类型, 而空类型是命题, 所以这个Π类型也是命题, 从而这句话良好地定义了 `X` 的一个子集.

注意这个Π类型 (全称量化) 提升了宇宙等级, 它比 `X` 高一个宇宙, 我们要用 `PR` 把它压下来. 可能可以使用宇宙多态的 `ℙ` 使得子集可以位于不同的宇宙, 从而不需要 `PR` 也应该可以证明康托尔定理. 但这会增加整个形式化的复杂度, 而且后续章节有必须使用 `PR` 的地方, 所以我们就干脆全局假设了 `PR`.

```agda
  A : ℙ X
  A x = Resize $ (∀ B → f B ≡ x → x ∉ B) , isPropΠ3 λ _ _ _ → isProp⊥
```

一旦对角线集 `A` 构造完成, 由定义立即有 `f A ∈ A` 蕴含 `f A ∉ A`.

```agda
  ∈→∉ : f A ∈ A → f A ∉ A
  ∈→∉ fA∈A = unresize fA∈A A refl
```

另一方面, 假设 `f A ∉ A`, 要证 `f A ∈ A`. 即假设有一个 `B` 满足 `f B ≡ f A`, 要证 `f A ∉ B`. 由 `f` 的单射性可知 `A ≡ B`, 用它改写前提 `f A ∉ A` 右边的 `A` 即证. ∎

```agda
  ∉→∈ : f A ∉ A → f A ∈ A
  ∉→∈ fA∉A = resize λ B fB≡ → transport (f A ∉_) (f-inj (sym fB≡)) fA∉A
```

## 单集

现在固定一个集合 `X`.

```agda
module Lemmas (X : Type ℓ) (X-set : isSet X) where
```

由 `X` 的某个项 `x` 所构成的单集 `｛ x ｝ : ℙ X` 定义为谓词 `x ≡_`. `X` 的集合性保证了 `x ≡_` 是一个谓词.

```agda
  opaque
    ｛_｝ : X → ℙ X
    ｛ x ｝ y = (x ≡ y) , transport isProp Path≡Eq (X-set _ _)
```

由 `_≡_` 的基本性质可以证明单集构造 `｛_｝` 具有单射性.

```agda
    ｛｝-inj : {x y : X} → ｛ x ｝ ≡ ｛ y ｝ → x ≡ y
    ｛｝-inj {x} {y} H = transport (idfun _) (sym $ ap fst $ happly H y) refl
```

我们说一个 `A : ℙ X` 是单集, 当且仅当它等于某个 `｛ x ｝`.

```agda
  is｛｝ : ℙ X → Type _
  is｛｝ A = Σ[ x ∈ X ] A ≡ ｛ x ｝
```

注意这里用的是Σ类型, 所以 "是单集" 并不是一个谓词, 而是一个集合, 实际上它就是由 `X` 的所有单集所构成的集合. 不过这无关紧要, 后面也不需要用到这一结论.

```agda
  isSetIs｛｝ : (A : ℙ X) → isSet (is｛｝ A)
  isSetIs｛｝ A = isSetΣ X-set λ x → isProp→isSet (transport isProp Path≡Eq $ isSetℙ A ｛ x ｝)
```

接着我们证明康托尔定理的一个变体, 说 `ℙ X` 的自嵌入一定射到了单集之外. 我们能实际构造出这个非单集, 用的还是对角线法, 证明的结构与 `Cantor-≰` 非常类似, 这里不再赘述.

```agda
  Cantor-beyond｛｝ : (f : ℙ X → ℙ X) → injective f → Σ[ A ∈ ℙ X ] ¬ is｛｝ (f A)
  Cantor-beyond｛｝ f f-inj = A , λ (x , fA≡) → noncontradiction (∈→∉ x fA≡) (∉→∈ x fA≡)
    where
    A : ℙ X
    A x = Resize $ (∀ B → f B ≡ ｛ x ｝ → x ∉ B) , isPropΠ3 λ _ _ _ → isProp⊥
    ∈→∉ : ∀ x → (f A ≡ ｛ x ｝) → x ∈ A → x ∉ A
    ∈→∉ x fA≡ x∈A = unresize x∈A A fA≡
    ∉→∈ : ∀ x → (f A ≡ ｛ x ｝) → x ∉ A → x ∈ A
    ∉→∈ x fA≡ x∉A = resize λ B fB≡ → transport (x ∉_) (f-inj (fA≡ ∙ sym fB≡)) x∉A
```

## 关键构造

```agda
  module _ (P : Type ℓ′) where

    Y = Σ[ A ∈ ℙ X ] (is｛｝ A ∨ Dec P)

    isSetY : isSet Y
    isSetY = isSetΣ isSetℙ λ _ → isProp→isSet squash₁

    X≤Y : X ≤ Y
    X≤Y = (λ x → ｛ x ｝ , inl (x , refl)) , ｛｝-inj ∘ (ap fst)

    dec→ℙX≤Y : Dec P → ℙ X ≤ Y
    dec→ℙX≤Y P-dec = (λ A → A , inr P-dec) , ap fst

    Y≰X : Y ≰ X
    Y≰X Y≤X@(f , f-inj) = DecNonEmpty P λ P-dec → Cantor-≰ X (≤-trans (dec→ℙX≤Y P-dec) Y≤X)

    Y≤ℙX : Y ≤ ℙ X
    Y≤ℙX = fst , λ fst-eq → Σ≡Prop (λ _ → squash₁Eq) fst-eq

    isCHType→ℙX≤Y : isCHType X Y → ∥ ℙ X ≤ Y ∥₁
    isCHType→ℙX≤Y ch-type = ch-type (X≤Y , Y≰X) Y≤ℙX

    ℙX≤Y→dec : isProp P → ℙ X ≤ Y → Dec P
    ℙX≤Y→dec P-prop ℙX≤Y with ℙX≤Y
    ... | (f , f-inj) with Cantor-beyond｛｝ (fst ∘ f) (f-inj ∘ (Σ≡Prop λ _ → squash₁Eq))
    ... | (A , ¬sing) with f A
    ... | (fA , sing∨dec) = ∥∥-rec (isPropDec P-prop)
      (λ { (_⊎_.inl sing) → ⊥-rec $ ¬sing sing
          ; (_⊎_.inr dec) → dec })
      sing∨dec

    isCHType→lem : isCHType X Y → isProp P → Dec P
    isCHType→lem ch-type P-prop = ∥∥-rec (isPropDec P-prop) (ℙX≤Y→dec P-prop) (isCHType→ℙX≤Y ch-type)
```

## 结论

```agda
CH→LEM : (∀ ℓ → CH ℓ) → (∀ ℓ → LEM ℓ)
CH→LEM ch ℓ P = isCHType→lem _ $ ch _ _ $ isSetY _
  where open Lemmas ℕ isSetℕ
```
