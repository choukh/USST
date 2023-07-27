---
title: 泛等结构集合论 (5) 吃自己:序数宇宙也是序数
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
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

前段是指序数 `α` 的底集 `⟨ α ⟩` 里小于某个上界 `a` 的那些元素, 它们具有类型 `B = Σ ⟨ α ⟩ (_≺ a)`, 且 `B` 也构成了一个序数, 记作 `α ↓ a`.

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
    {- 传递性 -} (λ _ _ _ x<y y<z → ≺-trans _ _ _ x<y y<z)
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
**证明** 假设 `α` 的两个前段满足 `α ↓ a ≤ α ↓ b`, 且有 `z ≺ a` 要证 `z ≺ b`. 从 `≤` 关系的证据中可以解构出序数嵌入 `f`, 它与前段嵌入的复合也是序数嵌入. 由序数嵌入的唯一性, `↑ ∘ f ≡ ↑`. 两边同时应用前段 `(z , z ≺ a)` 可得 `↑ (f $ z , z≺a) ≡ z`, 以此改写目标即证 `↑ (f $ z , z≺a) ≺ b`. 由于 `(f $ z , z≺a)` 是一个 `α ↓ b` 前段, 它显然 `≺ b`. ∎

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

**引理** 两个前段相等蕴含它们的上界相等.  
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

### 重要性质

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

## 严格序

(TODO)

```agda
_<_ : Ord 𝓊 → Ord 𝓊 → Type (𝓊 ⁺)
α < β = Σ b ∶ ⟨ β ⟩ , β ↓ b ≡ α
```

```agda
<→≤ : α < β → α ≤ β
<→≤ {β} (b , β↓b≡α) = subst (_≤ β) β↓b≡α ↓≤
```

(TODO)

```agda
↓-reflects-≺ : (a b : ⟨ α ⟩) → α ↓ a < α ↓ b → a ≺⟨ α ⟩ b
↓-reflects-≺ {α} a b ↓<↓ = subst (λ a → a ≺⟨ α ⟩ b) (sym eq) bounded
  where
  bnd : ⟨ α ↓ b ⟩
  bnd = ↓<↓ .fst
  bounded : ↑ bnd ≺⟨ α ⟩ b
  bounded = ↑-bounded bnd
  eq : a ≡ ↑ bnd
  eq = ↓-inj $ (sym $ ↓<↓ .snd) ∙ ↓≡↓ ↓≤

↓-preserves-≺ : (a b : ⟨ α ⟩) → a ≺⟨ α ⟩ b → α ↓ a < α ↓ b
↓-preserves-≺ a b a≺b = (a , a≺b) , ↓≡↓ ↓≤
```

### 性质

(TODO)

```agda
module _ {𝓊} where
  open BinaryRelation (_<_ {𝓊})
```

(TODO)

```agda
  <-prop : Propositional
  <-prop _ _ (b₁ , eq₁) (b₂ , eq₂) = Σ≡Prop
    (λ _ → isSetOrd _ _)
    (↓-inj $ eq₁ ∙ sym eq₂)
```

(TODO)

```agda
  <-trans : Transitive
  <-trans α β γ (b , β↓b≡α) β<γ = subst (_< γ) β↓b≡α β↓b<γ
    where
    β↓b<γ : (β ↓ b) < γ
    β↓b<γ = <→≤ β<γ .fst b , sym (↓≡↓ $ <→≤ β<γ)
```

(TODO)

```agda
  <-ext : Extensional
  <-ext α β H = ≃ₒ→≡ $ isoToEquiv i , mkIsOrderEquiv λ x y → isoToEquiv (j x y)
    where
    f : ∀ a → α ↓ a < β
    f a = H _ .fst (a , refl)
    g : ∀ b → β ↓ b < α
    g b = H _ .snd (b , refl)
    i : Iso ⟨ α ⟩ ⟨ β ⟩
    Iso.fun       i = fst ∘ f
    Iso.inv       i = fst ∘ g
    Iso.leftInv   i a = ↓-inj $ g _ .snd ∙ f a .snd
    Iso.rightInv  i b = ↓-inj $ f _ .snd ∙ g b .snd
    module _ x y where
      j : Iso (x ≺⟨ α ⟩ y) (Iso.fun i x ≺⟨ β ⟩ Iso.fun i y)
      Iso.fun       j H = ↓-reflects-≺ _ _ $ subst2 _<_ (sym $ f x .snd) (sym $ f y .snd) (↓-preserves-≺ _ _ H)
      Iso.inv       j H = ↓-reflects-≺ _ _ $ subst2 _<_ (f x .snd)       (f y .snd)       (↓-preserves-≺ _ _ H)
      Iso.leftInv   j _ = OrdStr.≺-prop (str α) _ _ _ _
      Iso.rightInv  j _ = OrdStr.≺-prop (str β) _ _ _ _
```

(TODO)

```agda
  <-wf : WellFounded
  <-wf α = acc λ β (a , α↓a≡β) → subst Acc α↓a≡β (Acc↓ a)
    where
    open OrdStr (str α)
    Acc↓ : (a : ⟨ α ⟩) → Acc (α ↓ a)
    Acc↓ = elim λ a IH → acc λ β ((b , b≺a) , α↓a↓b≡β) →
      subst Acc (sym (↓≡↓ ↓≤) ∙ α↓a↓b≡β) (IH b b≺a)
```

(TODO)

```agda
  <-irrefl : Irreflexive
  <-irrefl = WellFounded→Irreflexive <-wf
```

(TODO)

```agda
  <-wo : WellOrdered
  <-wo = mkWellOrdered <-prop <-trans <-ext <-wf
```

## 吃自己

(TODO)

```agda
Ω : ∀ {𝓊} → Ord (𝓊 ⁺)
Ω {𝓊} = Ord 𝓊 , mkOrdStr _<_ <-wo
```

(TODO)

```agda
_ : ⟨ Ω ⟩ ≡ Ord 𝓊
_ = refl
```

(TODO)

```agda
ordInOrd : {α : Ord 𝓊} → α ≃ₒ Ω ↓ α
ordInOrd {α} = isoToEquiv i , mkIsOrderEquiv λ x y → isoToEquiv (j x y)
  where
  open OrdStr
  i : Iso ⟨ α ⟩ ⟨ Ω ↓ α ⟩
  Iso.fun i x = α ↓ x , x , refl
  Iso.inv i (β , a , α↓a≡β) = a
  Iso.leftInv i _ = refl
  Iso.rightInv i (β , a , α↓a≡β) = ΣPathP $ α↓a≡β , isProp→PathP (λ _ → ≺-prop (str Ω) _ _) _ _
  module _ x y where
    j : Iso (x ≺⟨ α ⟩ y) (Iso.fun i x ≺⟨ Ω ↓ α ⟩ Iso.fun i y)
    Iso.fun       j = ↓-preserves-≺ _ _
    Iso.inv       j = ↓-reflects-≺ _ _
    Iso.leftInv   j _ = ≺-prop (str α) _ _ _ _
    Iso.rightInv  j _ = ≺-prop (str $ Ω ↓ α) (Iso.fun i x) (Iso.fun i y) _ _
```

## 布拉利-福尔蒂悖论

(TODO)

```agda
Burali-Forti : ¬ (Σ α ∶ Ord 𝓊 , α ≃ₒ Ω)
Burali-Forti (α , f) = <-irrefl _ (α , eq)
  where
  eq : Ω ↓ α ≡ Ω
  eq = ≃ₒ→≡ $ ≃ₒ-trans (≃ₒ-sym ordInOrd) f
```
