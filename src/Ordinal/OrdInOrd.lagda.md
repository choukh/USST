---
title: 泛等结构集合论 (5) 吃自己:序数宇宙也是序数
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
zhihu-url: https://zhuanlan.zhihu.com/p/646397707
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

前段是指序数 `α` 的底集 `⟨ α ⟩` 里小于某个上界 `a` 的那些元素, 它们具有类型

`B = Σ ⟨ α ⟩ (_≺ a)`

且 `B` 也构成了一个序数, 记作 `α ↓ a`.

```agda
infix 21 _↓_
_↓_ : (α : Ord 𝓊) → ⟨ α ⟩ → Ord 𝓊
α ↓ a = B , strB
  where
  open OrdStr (str α)
  B : Type _
  B = Σ ⟨ α ⟩ (_≺ a)
```

为了完成前段 `α ↓ a` 的构造, 我们还需要说明 `B` 具有序数结构 `strB`. 首先取原序数 `α` 的底序 `_≺_` 作为新序数 `α ↓ a` 的底序, 记作 `≺′`.

```agda
  _≺′_ : B → B → Type _
  (x , _) ≺′ (y , _) = x ≺ y
```

我们需要说明 `≺′` 也是良序, 即满足命题性, 传递性, 外延性和良基性. 其中命题性和传递性是显然的.

```agda
  strB : OrdStr B
  strB = mkOrdStr _≺′_ $ mkWellOrdered
    {- 命题性 -} (λ _ _ → ≺-prop _ _)
    {- 传递性 -} (λ _ _ _ → ≺-trans _ _ _)
```

对于外延性, 要证两个前段元素 `(x , x≺a)` 和 `(y , y≺a)` 相等. 已知前提 `H`, 它说对任意 `z ≺ a` 有 `z ≺ x ↔ z ≺ y`. 由于前段元素是依值配对, 且右边是命题, 只需证它们的左边相等. 用原序数 `α` 的底序 `_≺_` 的外延性 `≺-ext`, 要证 `x ≼ y` 且 `y ≼ x`. 假设 `z ≺ x`, 由传递性都有 `z ≺ a`, 由 `H` 即证 `z ≺ y`. 假设 `z ≺ y` 同理可证 `z ≺ x`.

```agda
    {- 外延性 -} (λ (x , x≺a) (y , y≺a) H → Σ≡Prop
      (λ _ → ≺-prop _ _)
      (≺-ext x y λ z → (λ z≺x → H (z , ≺-trans z x a z≺x x≺a) .fst z≺x)
                     , (λ z≺y → H (z , ≺-trans z y a z≺y y≺a) .snd z≺y)))
```

良基性的证明代码写起来相当简短, 但自然语言说起来比较绕. 我们要证任意前段元素 `(x , x ≺ a)` 在 `_≺′_` 关系下可及. 由良基归纳法, 有归纳假设: 对任意 `y ≺ x`, `(y , y ≺ a)` 可及. 现在要证 `(x , x ≺ a)`, 由可及的构造子 `acc`, 即证对任意 `(y , y ≺ a)`, 如果 `y ≺ x`, 那么 `(y , y ≺ a)` 可及. 由归纳假设即证.

```agda
    {- 良基性 -} (uncurry $ elim λ x IH x≺a → acc λ (y , y≺a) y≺x → IH y y≺x y≺a)
      where open BinaryRelation
```

### 前段嵌入

现在, 隐式给定序数 `α` 以及它的底集元素 `a`.

```agda
module _ {α : Ord 𝓊} {a : ⟨ α ⟩} where
  open OrdStr (str α)
```

我们知道 `α ↓ a` 的底集元素是依值配对, 考虑其左右投影.

左投影 `fst` 是前段 `α ↓ a` 底集到 `α` 底集的典范映射, 我们记为 `↑`, 并叫它前段嵌入.

```agda
  ↑ : ⟨ α ↓ a ⟩ → ⟨ α ⟩
  ↑ = fst
```

而右投影 `snd` 则可以取得 `↑ x ≺ a` 的证据, 说明前段元素 `x` 嵌入回原序数后不会超过 `a`.

```agda
  ↑-bounded : (x : ⟨ α ↓ a ⟩) → ↑ x ≺⟨ α ⟩ a
  ↑-bounded = snd
```

不难证明前段嵌入 `↑` 确实是一个序数嵌入.

```agda
  ↑-ordEmbed : IsOrdEmbed ↑
  ↑-ordEmbed = mkIsOrdEmbed (λ _ _ → idfun _)
    λ { b (a′ , a′≺a) b≺a′ → (b , ≺-trans _ _ _ b≺a′ a′≺a) , b≺a′ , refl }
```

前段嵌入 `↑` 配合上其序数嵌入性质 `↑-ordEmbed` 即是 `α ↓ a ≤ α` 的证明.

```agda
↓≤ : {a : ⟨ α ⟩} → α ↓ a ≤ α
↓≤ = ↑ , ↑-ordEmbed
```

### 单射性

**引理** 前段的 `≤` 关系反映它们上界的 `≼` 关系.  
**证明** 假设 `α` 的两个前段满足 `α ↓ a ≤ α ↓ b`, 且有 `z ≺ a` 要证 `z ≺ b`. 从 `≤` 关系的证据中可以解构出序数嵌入 `f`, 它与前段嵌入的复合也是序数嵌入. 由序数嵌入的唯一性, `↑ ∘ f ≡ ↑`. 两边同时应用前段 `(z , z ≺ a)` 可得

`↑ (f $ z , z≺a) ≡ z`

以此改写目标即证

`↑ (f $ z , z≺a) ≺ b`.

由于 `(f $ z , z≺a)` 是一个 `α ↓ b` 前段, 它显然 `≺ b`. ∎

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

**引理** 前段构造具有单射性, 即两个前段相等蕴含它们的上界相等.  
**证明** 用底序 `_≺_` 的外延性. 我们只证一边: `z ≺ a → z ≺ b`. 只需将前提 `α ↓ a ≡ α ↓ b` 弱化到 `α ↓ a ≤ α ↓ b`, 用上一条引理反映出 `a ≼ b` 即证. ∎

```agda
↓-inj : {a b : ⟨ α ⟩} → α ↓ a ≡ α ↓ b → a ≡ b
↓-inj {α} {a} {b} eq = ≺-ext a b λ z → ↓-reflects-≼ a b H₁ z , ↓-reflects-≼ b a H₂ z
  where
  open OrdStr (str α)
  H₁ : α ↓ a ≤ α ↓ b
  H₁ = subst (λ - → (α ↓ a) ≤ -) eq       ≤-refl
  H₂ : α ↓ b ≤ α ↓ a
  H₂ = subst (λ - → (α ↓ b) ≤ -) (sym eq) ≤-refl
```

### 前段的重要性质

下面是前段的一个重要性质, 它将不同序数的前段联系起来.

**引理** 序数 `α` 的 `a` 前段等价于被 `α` 通过某 `f` 所嵌入的另一个序数 `β` 的 `f a` 前段.  
**证明** 给定 `α` 到 `β` 的序数嵌入 `f` 以及 `α` 的底集元素 `a`, 要证 `α ↓ a ≃ₒ β ↓ (f a)`. 需要分别证明它们的底集等价且底序等价.

- 对于底集的等价, 我们构造同构来证明.
  - 正映射使用 `f` 及其保序性 `pres≺` 将 `(x , x≺a)` 映射到 `(f x , pres≺ _ _ x≺a)`.
  - 逆映射由 `f` 的"形成前段"性质 `formsInitSeg` 得到. 它对任意 `(y , y≺fa)` 都给出了一个 `(x , x≺a)`.
  - 两个方向的互逆性均由 `formsInitSeg` 的右分量可得.

```agda
↓≃ₒ↓ : ((f , _) : α ≤ β) (a : ⟨ α ⟩) → α ↓ a ≃ₒ β ↓ (f a)
↓≃ₒ↓ {α} {β} (f , emb) a = isoToEquiv i , mkIsOrderEquiv λ x y → isoToEquiv (j x y)
  where
  open OrdStr
  open IsOrdEmbed emb
  i : Iso ⟨ α ↓ a ⟩ ⟨ β ↓ f a ⟩
  Iso.fun       i (x , x≺a) = f x , pres≺ _ _ x≺a
  Iso.inv       i (y , y≺fa) = let (x , x≺a , _) = formsInitSeg _ _ y≺fa in x , x≺a
  Iso.leftInv   i (x , x≺a) = let (_ , _ , fw≡fx) = formsInitSeg _ _ (pres≺ _ _ x≺a) in
    Σ≡Prop (λ _ → ≺-prop (str α) _ _) (inj fw≡fx)
  Iso.rightInv  i (y , y≺fa) = let (_ , _ , fx≡y) = formsInitSeg _ _ y≺fa in
    Σ≡Prop (λ _ → ≺-prop (str β) _ _) fx≡y
```

- 对于底序的等价, 我们同样构造同构来证明.
  - 正映射都 `f` 的保序性 `pres≺` 得到.
  - 逆映射由 `f` 的"形成前段"性质 `formsInitSeg` 得到.
  - 两个方向的互逆性均由 `_≺_` 的命题性得到.

```agda
  module _ (u@(x , x≺a) v@(y , y≺fa) : ⟨ α ↓ a ⟩) where
    j : Iso (u ≺⟨ α ↓ a ⟩ v) (Iso.fun i u ≺⟨ β ↓ f a ⟩ Iso.fun i v)
    Iso.fun       j = pres≺ x y
    Iso.inv       j H = let (w , w≺y , fw≡fx) = formsInitSeg (f x) y H in
      subst (λ - → - ≺⟨ α ⟩ y) (inj fw≡fx) w≺y
    Iso.leftInv   j _ = ≺-prop (str α) _ _ _ _
    Iso.rightInv  j _ = ≺-prop (str β) _ _ _ _
```

**推论** 序数 `α` 的 `a` 前段**等于**被 `α` 通过某 `f` 所嵌入的另一个序数 `β` 的 `f a` 前段.  
**证明** 由上一条引理结合序数的泛等原理即证. ∎

```agda
↓≡↓ : ((f , _) : α ≤ β) {a : ⟨ α ⟩} → α ↓ a ≡ β ↓ (f a)
↓≡↓ f {a} = ≃ₒ→≡ $ ↓≃ₒ↓ f a
```

**推论** 对序数取两次前段等于取一次较短前段.  
**证明** 由上一条引理结合 `↓≤` 即证. ∎

```agda
↓↓-red : {a b : ⟨ α ⟩} {a≺b : a ≺⟨ α ⟩ b} → (α ↓ b) ↓ (a , a≺b) ≡ α ↓ a
↓↓-red = ↓≡↓ ↓≤
```

## 严格序

完善了前段的概念之后我们终于可以定义序数之间的严格序.

我们说 `α < β` 当且仅当存在 `β` 的一个前段 `β ↓ b` 等于 `α`. 注意这里说的"存在"在形式上是用Σ类型来表达的, 我们后面将证明 `_<_` 具有命题性, 而不需要对它做命题截断.

```agda
_<_ : Ord 𝓊 → Ord 𝓊 → Type (𝓊 ⁺)
α < β = Σ b ∶ ⟨ β ⟩ , β ↓ b ≡ α
```

如所期待的那样, `_<_` 可以弱化到 `_≤_`, 只需简单的改写即得.

```agda
<→≤ : α < β → α ≤ β
<→≤ {β} (b , β↓b≡α) = subst (_≤ β) β↓b≡α ↓≤
```

下面是引理 `↓≤` 的加强版, 由严格序的定义即得.

```agda
↓< : {a : ⟨ α ⟩} → α ↓ a < α
↓< {a} = a , refl
```

下面是 `↓-reflects-≼` 的严格序版本.

**引理** 前段的 `<` 关系反映它们上界的 `≺` 关系.  
**证明** 假设 `α` 的两个前段满足 `α ↓ a < α ↓ b`, 要证 `a ≺ b`. 严格序的证据承诺了 `α ↓ b` 底集的一个元素 `c` 满足

`(α ↓ b) ↓ c ≡ α ↓ a`

由前段的重要性质有

`(α ↓ b) ↓ c ≡ α ↓ ↑ c`

传递得

`α ↓ ↑ c ≡ α ↓ a`

由前段构造的单射性得 `↑ c ≡ a`. 由此改写目标即证 `↑ c ≺ b`. 由于 `c` 是 `α ↓ b` 的底集元素, 显然有 `↑ c ≺ b`. ∎

```agda
↓-reflects-≺ : (a b : ⟨ α ⟩) → α ↓ a < α ↓ b → a ≺⟨ α ⟩ b
↓-reflects-≺ {α} a b ↓<↓ = subst (λ a → a ≺⟨ α ⟩ b) (↓-inj eq) (↑-bounded c)
  where
  c : ⟨ α ↓ b ⟩
  c = ↓<↓ .fst
  eq : α ↓ ↑ c ≡ α ↓ a
  eq = sym ↓↓-red ∙ ↓<↓ .snd
```

**引理** 前段保持它们上界的 `≺` 关系.  
**证明** 假设 `a ≺ b`, 要证 `α ↓ a < α ↓ b`. 由前段的重要性质, 有前段元素 `(a , a≺b)` 满足

`(α ↓ b) ↓ (a , a≺b) ≡ α ↓ a`

此即 `<` 关系的证据. ∎

```agda
↓-preserves-≺ : (a b : ⟨ α ⟩) → a ≺⟨ α ⟩ b → α ↓ a < α ↓ b
↓-preserves-≺ a b a≺b = (a , a≺b) , ↓↓-red
```

### 性质

给定宇宙 `𝓊` 上的 `_<_` 关系.

```agda
module _ {𝓊} where
  open BinaryRelation (_<_ {𝓊})
```

**引理** `_<_` 具有命题性.  
**证明** 要证 `α < β` 的两个证据相等, 即证两个依值配对 `(b₁ , eq₁)` 和 `(b₂ , eq₂)` 相等. 其中右边具有类型

`eq₁ : β ↓ b₁ ≡ α` 以及

`eq₂ : β ↓ b₂ ≡ α`

由序数宇宙的集合性, 只要证明依值配对的左边相等, 右边就相等. 由 `eq₁` 和 `eq₂` 传递可得

`β ↓ b₁ ≡ β ↓ b₂`

再由前段构造的单射性即得 `b₁ ≡ b₂`. ∎

```agda
  <-prop : Propositional
  <-prop _ _ (b₁ , eq₁) (b₂ , eq₂) = Σ≡Prop (λ _ → isSetOrd _ _) (↓-inj $ eq₁ ∙ sym eq₂)
```

**引理** `_<_` 具有传递性.  
**证明** 假设 `α < β` 和 `β < γ`, 要证 `α < γ`. 解构 `α < β` 的证据有 `(b , β↓b≡α)`, 用右边改写目标即证 `β ↓ b < γ`.

将 `β < γ` 弱化为 `β ≤ γ`, 拿到它们之间的序数嵌入并应用到 `b`, 将所得记为 `c`, 它就是目标所要求的 `γ` 上界, 只要证

`γ ↓ c ≡ β ↓ b`

左右对调可以看出它是前段重要性质 `↓≡↓` 的实例, 因为满足其前提要求 `β ≤ γ` 且 `c` 为 `b` 的嵌入所得. ∎

```agda
  <-trans : Transitive
  <-trans α β γ (b , β↓b≡α) β<γ = subst (_< γ) β↓b≡α β↓b<γ
    where
    β↓b<γ : (β ↓ b) < γ
    β↓b<γ = <→≤ β<γ .fst b , sym (↓≡↓ $ <→≤ β<γ)
```

**引理** `_<_` 具有外延性.  
**证明** 假设对任意 `z` 都有 `z < α ↔ z < β`, 要证 `α ≡ β`. 用序数的泛等原理转化为证明 `α` 与 `β` 同构, 分别要证它们的底集同构且底序同构.

由前提和引理 `↓<` 我们有 `f : α ↓ a < β` 且 `g : β ↓ b < α`, 满足

`f₂ a : β ↓ (f₁ a) ≡ α ↓ a` 以及

`g₂ b : α ↓ (g₁ b) ≡ β ↓ b`

其中 `f₁` 和 `f₂` 指 `fst ∘ f` 和 `snd ∘ f`, 对 `g` 亦同.

`f₁` 和 `g₁` 即是 `⟨ α ⟩` 到 `⟨ β ⟩` 的正映射和逆映射. 互逆性结合 `f₂`, `g₂` 与前段构造的单射性可证.

```agda
  <-ext : Extensional
  <-ext α β H = ≃ₒ→≡ $ isoToEquiv i , mkIsOrderEquiv λ x y → isoToEquiv (j x y)
    where
    f : ∀ a → α ↓ a < β
    f a = H _ .fst ↓<
    g : ∀ b → β ↓ b < α
    g b = H _ .snd ↓<
    i : Iso ⟨ α ⟩ ⟨ β ⟩
    Iso.fun       i = fst ∘ f
    Iso.inv       i = fst ∘ g
    Iso.leftInv   i a = ↓-inj $ g _ .snd ∙ f _ .snd
    Iso.rightInv  i b = ↓-inj $ f _ .snd ∙ g _ .snd
```

对于底序的同构, 我们要建立 `≺⟨ α ⟩` 与 `≺⟨ β ⟩` 的同构. 无论正映射还是逆映射, 将一边输入到 `↓-preserves-≺`, 并用 `f₂` 和 `g₂` 改写成适用于 `↓-reflects-≺` 的形式, 再输入到它即得另一边. 互逆性由 `≺` 的命题性可证. ∎

```agda
    module _ x y where
      j : Iso (x ≺⟨ α ⟩ y) (Iso.fun i x ≺⟨ β ⟩ Iso.fun i y)
      Iso.fun       j H = ↓-reflects-≺ _ _ $ subst2 _<_ (sym $ f x .snd) (sym $ f y .snd) (↓-preserves-≺ _ _ H)
      Iso.inv       j H = ↓-reflects-≺ _ _ $ subst2 _<_ (f x .snd)       (f y .snd)       (↓-preserves-≺ _ _ H)
      Iso.leftInv   j _ = OrdStr.≺-prop (str α) _ _ _ _
      Iso.rightInv  j _ = OrdStr.≺-prop (str β) _ _ _ _
```

**引理** `_<_` 具有良基性.  
**证明** 要证任意 `α` 在 `_<_` 关系下可及. 由可及的构造子 `acc`, 即证对任意 `β < α`, `β` 可及. 目标可以改写为证任意 `α ↓ a` 都可及.

```agda
  <-wf : WellFounded
  <-wf α = acc λ β (a , α↓a≡β) → subst Acc α↓a≡β (Acc↓ a)
    where
    open OrdStr (str α)
    Acc↓ : (a : ⟨ α ⟩) → Acc (α ↓ a)
```

由良基归纳法, 有归纳假设: 对任意 `b ≺ a`, `α ↓ b` 可及. 现在要证 `α ↓ a`, 由可及的构造子 `acc`, 即证对任意 `β < α ↓ a`, `β` 可及.

`β < α ↓ a` 说明有 `b ≺ a` 满足

`α ↓ a ↓ b ≡ β`, 消掉一个 `↓` 有

`α ↓ b ≡ β`

由此改写目标, 即证 `α ↓ b` 可及. 由归纳假设即证. ∎

```agda
    Acc↓ = elim λ a IH → acc λ β ((b , b≺a) , α↓a↓b≡β) →
      subst Acc (sym ↓↓-red ∙ α↓a↓b≡β) (IH b b≺a)
```

`_<_` 的良基性蕴含其反自反性.

```agda
  <-irrefl : Irreflexive
  <-irrefl = WellFounded→Irreflexive <-wf
```

`_<_` 的命题, 传递, 外延和良基性说明它是一个良序关系.

```agda
  <-wo : WellOrdered
  <-wo = mkWellOrdered <-prop <-trans <-ext <-wf
```

## 吃自己

序数宇宙 `Ord 𝓊` 配合上其上的良序 `_<_` 说明它本身也构成一个序数, 我们记作 `Ω`, 它位于 `Ord (𝓊 ⁺)` 序数宇宙.

```agda
Ω : ∀ {𝓊} → Ord (𝓊 ⁺)
Ω {𝓊} = Ord 𝓊 , mkOrdStr _<_ <-wo
```

序数 `Ω` 的底集 `⟨ Ω ⟩` 即序数宇宙 `Ord 𝓊`. 这两种记法可以互换使用.

```agda
_ : ⟨ Ω ⟩ ≡ Ord 𝓊
_ = refl
```

集合论中有结论说"序数是比它小的所有序数所组成的集合", 以下是它在类型论中的对应物.

**定理** 序数 `α` 等价于 `Ω` 的 `α` 前段.  
**证明** 与 `↓≃ₒ↓` 和 `<-ext` 的证明类似地, 我们分别证明底集同构且底序同构.

- 底集的同构构造如下
  - 正映射: 将 `a : ⟨ α ⟩` 映射到 `(α ↓ a , ↓<) : ⟨ Ω ↓ α ⟩` 即可. (其中 `↓<` 具有 `(a , refl)` 的形式)
  - 逆映射: `⟨ Ω ↓ α ⟩` 的项是三元组 `(β , a , α↓a≡β)`, 取第二分量即可.
  - 左互逆性: 计算即得.
  - 右互逆性: 取第三分量 `α↓a≡β` 即得.

```agda
α≃Ω↓α : {α : Ord 𝓊} → α ≃ₒ Ω ↓ α
α≃Ω↓α {α} = isoToEquiv i , mkIsOrderEquiv λ x y → isoToEquiv (j x y)
  where
  open OrdStr
  i : Iso ⟨ α ⟩ ⟨ Ω ↓ α ⟩
  Iso.fun i a = α ↓ a , ↓<
  Iso.inv i (β , a , α↓a≡β) = a
  Iso.leftInv i _ = refl
  Iso.rightInv i (β , a , α↓a≡β) = Σ≡Prop (λ _ → <-prop _ _) α↓a≡β
```

底序同构的正映射和逆映射正好由 `↓-preserves-≺` 和 `↓-reflects-≺` 提供. 互逆性由 `≺` 的命题性即证.

```agda
  module _ x y where
    j : Iso (x ≺⟨ α ⟩ y) (Iso.fun i x ≺⟨ Ω ↓ α ⟩ Iso.fun i y)
    Iso.fun       j = ↓-preserves-≺ _ _
    Iso.inv       j = ↓-reflects-≺ _ _
    Iso.leftInv   j _ = ≺-prop (str α) _ _ _ _
    Iso.rightInv  j _ = ≺-prop (str $ Ω ↓ α) (Iso.fun i x) (Iso.fun i y) _ _
```

## 布拉利-福尔蒂悖论

布拉利-福尔蒂悖论又叫最大序数悖论, 是朴素集合论中发现的第一个悖论, 比罗素悖论还早. 它说

> 设Ord是所有序数的集合, 那么Ord对应一个序数Ω, 它比Ord里面的序数都大. 又Ω也在Ord中, 有 Ω < Ω, 违反 < 的反自反性

ZFC 集合论的解决方案是说 Ord 不是集合. 类型论中的解决方案则是宇宙分层, Ω 不在 Ord 𝓊 中, 而在 Ord (𝓊 ⁺) 中, 对应于以下定理.

**定理** `Ω` 不与其中的任意 `α` 等价.  
**证明** 假设存在 `α` 满足 `α ≃ₒ Ω`, 由上一条定理有 `α ≃ₒ Ω ↓ α`. 由等价的对称性和传递性有 `Ω ↓ α ≃ₒ Ω`, 再用序数的泛等原理有 `Ω ↓ α ≡ Ω`. 因此 `Ω < Ω`, 违反 `<` 的反自反性. ∎

```agda
Burali-Forti : ¬ (Σ α ∶ ⟨ Ω {𝓊} ⟩ , α ≃ₒ Ω)
Burali-Forti (α , f) = <-irrefl _ Ω<Ω
  where
  eq : Ω ↓ α ≡ Ω
  eq = ≃ₒ→≡ $ ≃ₒ-trans (≃ₒ-sym α≃Ω↓α) f
  Ω<Ω : Ω < Ω
  Ω<Ω = α , eq
```
