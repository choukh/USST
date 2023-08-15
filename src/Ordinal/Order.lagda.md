---
title: 泛等结构集合论 (5) 序数的序
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
zhihu-url: https://zhuanlan.zhihu.com/p/644984990
---

# 泛等结构集合论 (5) 序数的序

> 交流Q群: 893531731  
> 本文源码: [Ordinal.Order.lagda.md](https://github.com/choukh/USST/blob/main/src/Ordinal/Order.lagda.md)  
> 高亮渲染: [Ordinal.Order.html](https://choukh.github.io/USST/Ordinal.Order.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification --hidden-argument-puns #-}

module Ordinal.Order where
open import Preliminary
open import Ordinal.Base
```

## 序数嵌入

现在考虑序数底集间的一种特殊的嵌入, 由于它如此特殊以至于对于序数我们只会谈论这一种嵌入, 我们就用"序数嵌入"作为正式术语 (在 HoTT Book 上叫 simulation).

序数嵌入要求两个条件, 一是保序, 二是它的像向下封闭, 或者说, 能形成一个前段.

```agda
record IsOrdEmbed {α : Ord 𝓊} {β : Ord 𝓋} (f : ⟨ α ⟩ → ⟨ β ⟩) : Type (𝓊 ⊔ 𝓋) where
  constructor mkIsOrdEmbed
  field
    pres≺ : ∀ a a′ → a ≺⟨ α ⟩ a′ → f a ≺⟨ β ⟩ f a′
    formsInitSeg : ∀ b a′ → b ≺⟨ β ⟩ f a′ → Σ a ∶ ⟨ α ⟩ , a ≺⟨ α ⟩ a′ × f a ≡ b
```

保序性 `pres≺` 很简单, 它就是上一章序等价 `hPres≺` 的弱化版. "形成前段" `formsInitSeg` 这一性质的直观可以参考下图. 它说只要一个底集元素被射到, 那么比它小的元素都会被射到, 也就是映射的像能形成 `≺` 的一个前段.

```string
... a   ... ≺₁ ... a′  ...  
    |              |  
  f |            f |  
    ↓              ↓  
... f a ... ≺₂ ... f a′ ...  
```

### 单射性

**引理** 序数嵌入是单射.  
**证明** 用双参数形式的良基消去 `elim2`, 拿到归纳假设

`IH : ∀ u v → u ≺ x → v ≺ y → f u ≡ f v → u ≡ v`,

要证 `f x ≡ f y → x ≡ y`.

```agda
  inj : injective f
  inj = elim2 aux _ _
    where
    open OrdStr (str α) using (≺-ext; elim2)

    aux : ∀ x y → (∀ u v → u ≺⟨ α ⟩ x → v ≺⟨ α ⟩ y → f u ≡ f v → u ≡ v) → f x ≡ f y → x ≡ y
```

用 `≺` 的外延性, 要证两种对称的情况 `p` 和 `q`, 我们只证 `p : ∀ z → z ≺ x → z ≺ y`.

```agda
    aux x y IH fx≡fy = ≺-ext x y λ z → →: p z ←: q z
      where
      p : ∀ z → z ≺⟨ α ⟩ x → z ≺⟨ α ⟩ y
```

由 `z ≺ x` 及嵌入的保序性有 `f z ≺ f x ≡ f y`.

由于嵌入能形成前段, 必有一个 `w` 满足 `w ≺ y` 且 `f w ≡ f z`.

再结合归纳假设有 `w ≡ z`, 改写目标即证 `w ≺ y`, 此乃前提.

```agda
      p z z≺x = subst (λ - → - ≺⟨ α ⟩ y) w≡z w≺y
        where
        fz≺fy : f z ≺⟨ β ⟩ f y
        fz≺fy = subst (λ - → f z ≺⟨ β ⟩ -) fx≡fy (pres≺ z x z≺x)
        Σw : Σ w ∶ ⟨ α ⟩ , (w ≺⟨ α ⟩ y × f w ≡ f z)
        Σw = formsInitSeg (f z) y fz≺fy
        w = fst Σw
        w≺y = fst $ snd Σw
        fw≡fz = snd $ snd Σw
        w≡z : w ≡ z
        w≡z = sym $ IH z w z≺x w≺y (sym fw≡fz)
```

`q` 同理可证. ∎

```agda
      q : ∀ z → z ≺⟨ α ⟩ y → z ≺⟨ α ⟩ x
      q z z≺y = subst (λ - → - ≺⟨ α ⟩ x) w≡z w≺x
        where
        fz≺fx : f z ≺⟨ β ⟩ f x
        fz≺fx = subst (λ - → f z ≺⟨ β ⟩ -) (sym fx≡fy) (pres≺ z y z≺y)
        Σw : Σ w ∶ ⟨ α ⟩ , (w ≺⟨ α ⟩ x × f w ≡ f z)
        Σw = formsInitSeg (f z) x fz≺fx
        w = fst Σw
        w≺x = fst $ snd Σw
        fw≡fz = snd $ snd Σw
        w≡z : w ≡ z
        w≡z = IH w z w≺x z≺y fw≡fz
```

### 命题性

易证保序性是命题.

```agda
  isPropPres≺ : ∀ a a′ → a ≺⟨ α ⟩ a′ → isProp (f a ≺⟨ β ⟩ f a′)
  isPropPres≺ _ _ _ = ≺-prop _ _
    where open OrdStr (str β) using (≺-prop)
```

**引理** "形成前段"是命题, 尽管没有截断.  
**证明** 由于前段性是命题, 只需证 `b` 对应的 `α` 前段唯一. 假设有两个这样的前段, 分别有端点 `x` 和 `y` 被 `f` 射到 `b`, 由嵌入的单射性 `x ≡ y`. ∎

```agda
  isPropFormsInitSeg : ∀ b a′ → b ≺⟨ β ⟩ f a′ → isProp (Σ a ∶ ⟨ α ⟩ , (a ≺⟨ α ⟩ a′) × (f a ≡ b))
  isPropFormsInitSeg b a′ b≺fa′ (x , x≺a′ , fx≡b) (y , y≺a′ , fy≡b) = Σ≡Prop
    (λ _ → isProp× (≺-prop _ _) (underlying-set _ _))
    (inj (fx≡b ∙ sym fy≡b))
    where
    open OrdStr (str α) using (≺-prop)
    open OrdStr (str β) using (underlying-set)
```

于是嵌入性是命题.

```agda
isPropIsOrdEmbed : {α : Ord 𝓊} {β : Ord 𝓋} (f : ⟨ α ⟩ → ⟨ β ⟩) → isProp (IsOrdEmbed f)
isPropIsOrdEmbed {α} {β} f = isOfHLevelRetractFromIso 1 IsOrdEmbedIsoΣ $ aux
  where
  unquoteDecl IsOrdEmbedIsoΣ = declareRecordIsoΣ IsOrdEmbedIsoΣ (quote IsOrdEmbed)
  aux : ∀ x y → x ≡ y
  aux x _ = ΣPathP (isPropΠ3 isPropPres≺ _ _ , isPropΠ3 isPropFormsInitSeg _ _)
    where open IsOrdEmbed {α = α} {β} (Iso.inv IsOrdEmbedIsoΣ x)
```

### 唯一性

**引理** 给定两个序数, 它们之间的嵌入唯一.  
**证明** 用函数的外延性以及底序的外延性, 使用与嵌入的单射性的证明类似的改写即证. ∎

```
ordEmbed-unique : {α : Ord 𝓊} {β : Ord 𝓊′}
  (f g : ⟨ α ⟩ → ⟨ β ⟩) → IsOrdEmbed f → IsOrdEmbed g → f ≡ g
ordEmbed-unique {α} {β} f g f-emb g-emb =
  funExt $ elim λ x IH → ≺-ext (f x) (g x) λ z →
    →: (λ z≺fx → let (a , a≺x , fa≡z) = formsInitSeg f-emb z x z≺fx in
      subst (_≺ g x) (sym (IH a a≺x) ∙ fa≡z) (pres≺ g-emb a x a≺x))
    ←: (λ z≺gx → let (a , a≺x , ga≡z) = formsInitSeg g-emb z x z≺gx in
      subst (_≺ f x) (IH a a≺x ∙ ga≡z) (pres≺ f-emb a x a≺x))
  where open IsOrdEmbed
        open OrdStr (str α) using (elim)
        open OrdStr (str β) using (≺-ext; _≺_)
```

**引理** 序数等价也是一个序数嵌入.  
**证明** 要证序数等价的底层函数 `f` 保序且形成前段. 保序性即 `hPres≺` 的底层函数. 对任意 `b ≺ f a′`, 有 `f (f⁻¹ b) ≡ b`, 改写可得 `f (f⁻¹ b) ≺ f a′`, 再用 `hPres≺⁻¹` 即得 `(f⁻¹ b) ≺ a′`. 于是 `f⁻¹ b` 就是"形成前段"条件所要求的 `a`. ∎

```agda
IsOrdEquiv→IsOrdEmbed : (f : ⟨ α ⟩ ≃ ⟨ β ⟩) → IsOrdEquiv (str α) f (str β) → IsOrdEmbed (f ⁺¹)
IsOrdEquiv→IsOrdEmbed {β} f ordEquiv = mkIsOrdEmbed
  (λ a a′ → hPres≺ a a′ ⁺¹)
  (λ b a′ b≺fa′ → (f ⁻¹) b
    , (hPres≺ _ a′ ⁻¹) (subst (λ - → - ≺⟨ β ⟩ _) (sym $ secIsEq (snd f) b) b≺fa′)
    , secIsEq (snd f) b)
  where open IsOrdEquiv ordEquiv
```

**引理** 给定两个序数, 它们之间的序数等价唯一.  
**证明** 由于"是序数等价"是命题, 只需证该等价的底层函数唯一. 又序数等价也是序数嵌入, 由序数嵌入的唯一性得证. ∎

```agda
isPropOrdEquiv : (α : Ord 𝓊) (β : Ord 𝓊′) → isProp (α ≃ₒ β)
isPropOrdEquiv α β (f , f-ordEquiv) (g , g-ordEquiv) = Σ≡Prop
  (λ _ → isPropIsOrdEquiv _ _ _)
  (equivEq $ ordEmbed-unique (f ⁺¹) (g ⁺¹)
    (IsOrdEquiv→IsOrdEmbed f f-ordEquiv)
    (IsOrdEquiv→IsOrdEmbed g g-ordEquiv))
```

**推论** 序数宇宙是集合.  
**证明** 即证两个序数的相等是命题, 由序数的泛等原理, 这等价于证两个序数间的等价唯一. ∎

```agda
isSetOrd : isSet (Ord 𝓊)
isSetOrd α β = (equiv ⁺¹) (isOfHLevelLift 1 $ isPropOrdEquiv α β)
  where
  equiv : isProp (Lift (α ≃ₒ β)) ≃ isProp (α ≡ β)
  equiv = cong≃ isProp $ compEquiv (invEquiv LiftEquiv) (OrdPath α β)
```

### 嵌入序数

我们称一个配备了序关系 `_≺_` 的类型 `carrier` (它在满足接下来给出的条件后会自动成为一个集合) 构成了一个到序数 `target` 的**嵌入序数 (`EmbedOrd`)**, 当且仅当 `carrier` 到 `target` 底集的映射 `embed` 满足:

1. `inj` : 具有单射性
2. `pres≺` : 保序
3. `formsInitSeg` : 能形成前段

```agda
record EmbedOrd 𝓊 𝓋 : Type (𝓊 ⁺ ⊔ 𝓋 ⁺) where
  field
    carrier : Type 𝓊
    _≺_ : carrier → carrier → Type 𝓊
    relation-prop : ∀ x y → isProp (x ≺ y)
    target : Ord 𝓋
    embed : carrier → ⟨ target ⟩
    inj : injective embed
    pres≺ : ∀ a a′ → a ≺ a′ → embed a ≺⟨ target ⟩ embed a′
    formsInitSeg : ∀ b a′ → b ≺⟨ target ⟩ embed a′ → Σ a ∶ carrier , a ≺ a′ × embed a ≡ b
```

**引理** 嵌入序数到序数有一个典范映射, 它将嵌入序数映射到以 `carrier` 为底集, `_≺_` 为底序的序数. 

```agda
tieup : EmbedOrd 𝓊 𝓋 → Ord 𝓊
tieup embedded = carrier , mkOrdStr _≺_ wo
```

**证明** 我们用 `f` 表示嵌入映射, `≺-trans` 和 `≺-ext` 指 `target` 底序的传递性和外延性, `elim` 指 `target` 底集的良基消去.

```agda
  where
  open EmbedOrd embedded renaming (embed to f)
  open OrdStr (str target) using (≺-trans; ≺-ext; elim)
  open BinaryRelation _≺_
```

我们需要说明 `_≺_` 是良序, 即满足命题性, 传递性, 外延性和良基性. 其中命题性是显然的.

```agda
  wo : WellOrdered
  WellOrdered.≺-prop  wo _ _ = relation-prop _ _
```

对于传递性, 假设 `x ≺ y` 和 `y ≺ z`, 由保序性有 `f x ≺ f y` 和 `f y ≺ f z`.

由 `target` 底序的传递性 `≺-trans` 有 `f x ≺ f z`.

由"形成前段"性, 存在 `x′ ≺ z` 满足 `f x′ ≡ f x`.

由 `f` 的单射性有 `x′ ≡ x`, 改写即得 `x ≺ z`.

```agda
  WellOrdered.≺-trans wo x y z x≺y y≺z =
    let fx≺fz : f x ≺⟨ target ⟩ f z
        fx≺fz = ≺-trans _ _ _ (pres≺ _ _ x≺y) (pres≺ _ _ y≺z)
        (x′ , x′≺z , fx′≡fx) = formsInitSeg _ _ fx≺fz
    in subst (_≺ z) (inj fx′≡fx) x′≺z
```

对于外延性, 假设 `H : ∀ z → z ≺ x ↔ z ≺ y`, 要证 `x ≡ y`.

由 `f` 的单射性我们证 `f x ≡ f y`.

又由 `target` 底序的外延性 `≺-ext` 只需证对任意 `z` 都有 `z ≺ f x ↔ z ≺ f y`.

我们只证左到右: 假设 `z ≺ f x`, 要证 `z ≺ f y`.

由"形成前段"性, 存在 `x′ ≺ x` 满足 `f x′ ≡ z`, 改写目标即证 `f x′ ≺ f y`.

由保序性只需证 `x′ ≺ y`. 由前提 `x′ ≺ x` 和 `H` 即得.

```agda
  WellOrdered.≺-ext wo x y H = inj $ ≺-ext (f x) (f y) λ z →
    →: (λ z≺fx → let (x′ , x′≺x , fx′≡z) = formsInitSeg _ _ z≺fx in
      subst (λ z → z ≺⟨ target ⟩ f y) fx′≡z $ pres≺ _ _ $ H _ .to   x′≺x)
    ←: (λ z≺fy → let (y′ , y′≺y , fy′≡z) = formsInitSeg _ _ z≺fy in
      subst (λ z → z ≺⟨ target ⟩ f x) fy′≡z $ pres≺ _ _ $ H _ .from y′≺y)
```

对于良基性, 需要仔细选取辅助命题 `aux` 的形式. 我们先证任意满足 `f x ≡ y` 的 `x` 可及.

条件 `f x ≡ y` 看似多余, 但其实对于良基消去的使用是必须的.

一旦此 `aux` 完成, 那么对任意 `x` 令 `y` 为 `f x` 就可以得到 `x` 可及, 也就完成了良基性的证明.

```agda
  WellOrdered.≺-wf wo x = aux (f x) refl where
    aux : ∀ y {x} (eq : f x ≡ y) → Acc x
```

最后我们证 `aux`. 用良基消去, 假设任意满足 `f x ≡ y` 的 `x` 和 `y`, 有归纳假设 "对任意 `v ≺ y` , 如果有 `f u ≡ v`, 那么 `u` 可及", 要证 `x` 可及.

用构造子 `acc`, 我们证任意 `z ≺ x` 可及. 用归纳假设, 令 `u` 为 `z`, `v` 为 `f z`, 只需证 `f z ≺ y`.

用 `f x ≡ y` 改写即证 `f z ≺ f x`. 由前提 `z ≺ x` 和保序性得证. ∎

```agda
    aux = elim λ y IH eq → acc λ z z≺x → IH (f z)
      (subst (λ y → f z ≺⟨ target ⟩ y) eq (pres≺ _ _ z≺x)) refl
```

## 序数宇宙降级

假设 `PR`, 利用嵌入序数, 我们可以将任意 `β : Ord 𝓋` 降级到 `Ord 𝓊` 上, 只要找到一个 `A : Type 𝓊` 满足 `A ≃ ⟨ β ⟩`.

```agda
module _ ⦃ _ : PR ⦄ (A : Type 𝓊) (β : Ord 𝓋) (f : A ≃ ⟨ β ⟩) where

  ResizeOrd : Ord 𝓊
  ResizeOrd = tieup emb
    where
    open OrdStr (str β)
    _<ₕ_ : A → A → hProp 𝓊
    x <ₕ y = Resize ((f ⁺¹) x ≺⟨ β ⟩ (f ⁺¹) y , ≺-prop _ _)
    emb : EmbedOrd 𝓊 𝓋
    EmbedOrd.carrier       emb = A
    EmbedOrd._≺_           emb = fst ∘₂ _<ₕ_
    EmbedOrd.relation-prop emb = str ∘₂ _<ₕ_
    EmbedOrd.target        emb = β
    EmbedOrd.embed         emb = f ⁺¹
    EmbedOrd.inj           emb = equivFunInjective f
    EmbedOrd.pres≺         emb _ _ = unresize
    EmbedOrd.formsInitSeg  emb b a′ b≺fa′ = (f ⁻¹) b , resize H , secIsEq (snd f) b where
      H : (f ⁺¹ ∘ f ⁻¹) b ≺ (f ⁺¹) a′
      H = subst (_≺ (f ⁺¹) a′) (sym $ secIsEq (snd f) b) b≺fa′
```

降级后的序数与原序数等价, 因为反降级函数 `unresize` 是同伦等价.

```agda
  ResizeOrdEquiv : ResizeOrd ≃ₒ β
  ResizeOrdEquiv = f , mkIsOrderEquiv λ _ _ → unresize , isEquivUnresize
```

## 序数宇宙提升

序数宇宙提升的方法也类似, 而且更为简单, 直接用 `Lift` 即可.

```agda
module _ (α : Ord 𝓊) {𝓋 : Level} where

  LiftOrd : Ord (𝓊 ⊔ 𝓋)
  LiftOrd = tieup emb
    where
    open OrdStr (str α)
    _<_ : Lift ⟨ α ⟩ → Lift ⟨ α ⟩ → Type (𝓊 ⊔ 𝓋)
    lift x < lift y = Lift {j = 𝓋} (x ≺ y)
    emb : EmbedOrd (𝓊 ⊔ 𝓋) 𝓊
    EmbedOrd.carrier       emb = Lift {j = 𝓋} ⟨ α ⟩
    EmbedOrd._≺_           emb = _<_
    EmbedOrd.relation-prop emb _ _ = isOfHLevelLift 1 (≺-prop _ _)
    EmbedOrd.target        emb = α
    EmbedOrd.embed         emb = lower
    EmbedOrd.inj           emb = liftExt
    EmbedOrd.pres≺         emb _ _ = lower
    EmbedOrd.formsInitSeg  emb b (lift a′) b≺fa′ = lift b , lift b≺fa′ , refl
```

序数与提升后的序数等价.

```agda
  LiftOrdEquiv : α ≃ₒ LiftOrd
  LiftOrdEquiv = LiftEquiv , mkIsOrderEquiv λ x y → lift , LiftEquiv .snd
```

序数宇宙提升的用处之一是我们可以对实例化到不同宇宙的宇宙多态关系建立等价, 只要它们谈论的序数分别等价. 这会在后面几章用到.

```agda
cong≃ₒ : {α : Ord 𝓊} {β : Ord 𝓋} (P : {𝓊 : Level} → Ord 𝓊 → Type (𝓊 ⊔ 𝓌)) →
  α ≃ₒ β → P α ≃ P β
cong≃ₒ {𝓊} {𝓋} {α} {β} P α≃ₒβ =
  P α           ≃⟨ {!   !} ⟩
  P (LiftOrd α) ≃⟨ pathToEquiv (cong P Lα≡Lβ) ⟩
  P (LiftOrd β) ≃⟨ {!   !} ⟩
  P β           ≃∎
  where
  Lα≡Lβ : LiftOrd α {𝓋} ≡ LiftOrd β {𝓊}
  Lα≡Lβ = ≃ₒ→≡ $
    LiftOrd α ≃ₒ˘⟨ LiftOrdEquiv α ⟩
    α         ≃ₒ⟨ α≃ₒβ ⟩
    β         ≃ₒ⟨ LiftOrdEquiv β ⟩
    LiftOrd β ≃ₒ∎

cong≃ₒ₂ : {α β : Ord 𝓊} {γ δ : Ord 𝓋} (R : {𝓊 𝓋 : Level} → Ord 𝓊 → Ord 𝓋 → Type (𝓊 ⊔ 𝓋)) →
  α ≃ₒ γ → β ≃ₒ δ → R α β ≃ R γ δ
cong≃ₒ₂ {𝓊} {𝓋} {α} {β} {γ} {δ} R α≃ₒγ β≃ₒδ =
  R α β                     ≃⟨ cong≃ₒ {𝓌 = 𝓊} (λ α → R α β) (LiftOrdEquiv α) ⟩
  R (LiftOrd α) β           ≃⟨ cong≃ₒ {𝓌 = 𝓊 ⊔ 𝓋} (R (LiftOrd α)) (LiftOrdEquiv β) ⟩
  R (LiftOrd α) (LiftOrd β) ≃⟨ pathToEquiv $ cong₂ R Lα≡Lγ Lβ≡Lδ ⟩
  R (LiftOrd γ) (LiftOrd δ) ≃⟨ {!   !} ⟩
  R γ δ                     ≃∎
  where
  Lα≡Lγ : LiftOrd α {𝓋} ≡ LiftOrd γ {𝓊}
  Lα≡Lγ = ≃ₒ→≡ $
    LiftOrd α ≃ₒ˘⟨ LiftOrdEquiv α ⟩
    α         ≃ₒ⟨ α≃ₒγ ⟩
    γ         ≃ₒ⟨ LiftOrdEquiv γ ⟩
    LiftOrd γ ≃ₒ∎
  Lβ≡Lδ : LiftOrd β {𝓋} ≡ LiftOrd δ {𝓊}
  Lβ≡Lδ = ≃ₒ→≡ $
    LiftOrd β ≃ₒ˘⟨ LiftOrdEquiv β ⟩
    β         ≃ₒ⟨ β≃ₒδ ⟩
    δ         ≃ₒ⟨ LiftOrdEquiv δ ⟩
    LiftOrd δ ≃ₒ∎
```

## 非严格序

序数之间的非严格序 `_≤_` 定义为它们之间的嵌入的全体.

```agda
_≤_ : Ord 𝓊 → Ord 𝓋 → Type (𝓊 ⊔ 𝓋)
α ≤ β = Σ (⟨ α ⟩ → ⟨ β ⟩) IsOrdEmbed
```

因为嵌入是唯一的, 所以 `_≤_` 是命题.

```agda
≤-prop : (α : Ord 𝓊) (β : Ord 𝓋) → isProp (α ≤ β)
≤-prop α β (f , f-emb) (g , g-emb) = Σ≡Prop isPropIsOrdEmbed
  (ordEmbed-unique f g f-emb g-emb)
```

我们会在下一章定义了前段序数之后再定义严格序.

### 性质

我们证明 `≤` 确实是我们期望的非严格偏序, 即要证它满足自反, 传递, 和反对称性.

`≤` 满足自反性, 因为恒等函数满足序数嵌入的条件.

```agda
≤-refl : α ≤ α
≤-refl = idfun _ , mkIsOrdEmbed (λ a a′ a≺a′ → a≺a′) λ b a′ b≺a′ → b , b≺a′ , refl
```

`≤` 满足传递性, 因为复合函数满足序数嵌入的条件.

```agda
≤-trans : α ≤ β → β ≤ γ → α ≤ γ
≤-trans {α} {β} {γ} (f , f-emb) (g , g-emb) = g ∘ f , mkIsOrdEmbed
  (λ a a′ a≺a′ → pres≺ g-emb (f a) (f a′) (pres≺ f-emb a a′ a≺a′)) aux
  where
  open IsOrdEmbed
  aux : ∀ c a′ → c ≺⟨ γ ⟩ g (f a′) → Σ a ∶ ⟨ α ⟩ , a ≺⟨ α ⟩ a′ × g (f a) ≡ c
  aux c a′ c≺gfa = Σa .fst , Σa .snd .fst , cong g (Σa .snd .snd) ∙ Σb .snd .snd
    where
    Σb : Σ b ∶ ⟨ β ⟩ , b ≺⟨ β ⟩ f a′ × g b ≡ c
    Σb = formsInitSeg g-emb c (f a′) c≺gfa
    Σa : Σ a ∶ ⟨ α ⟩ , a ≺⟨ α ⟩ a′ × f a ≡ Σb .fst
    Σa = formsInitSeg f-emb (Σb .fst) a′ (Σb .snd .fst)
```

为了证明 `≤` 反对称, 我们先证双向嵌入蕴含等价, 再用泛等原理换到 `≡`.

**引理** 双向嵌入蕴含等价.  
**证明** 两个方向的序数嵌入正好充当了序数等价的正映射和逆映射, 并且序数嵌入的唯一性保证了这两个映射是互逆的. 两个方向的序数嵌入的保序性正当提供了序等价的正映射和逆映射, 并且底序的命题性保证了它们是互逆的. ∎

```agda
≤-antisym-≃ₒ : α ≤ β → β ≤ α → α ≃ₒ β
≤-antisym-≃ₒ {α} {β} α≤β@(f , f-emb) β≤α@(g , g-emb) =
  isoToEquiv (iso f g sec ret) , mkIsOrderEquiv λ x y → isoToEquiv (iso
    (pres≺ f-emb x y)
    (subst2 (underlyingRel α) (ret x) (ret y) ∘ (pres≺ g-emb _ _))
    (λ _ → ≺-prop (str β) _ _ _ _)
    (λ _ → ≺-prop (str α) _ _ _ _))
  where
  sec : section f g
  sec = funExt⁻ $ ordEmbed-unique (f ∘ g) (idfun _) (snd $ ≤-trans β≤α α≤β) (snd ≤-refl)
  ret : retract f g
  ret = funExt⁻ $ ordEmbed-unique (g ∘ f) (idfun _) (snd $ ≤-trans α≤β β≤α) (snd ≤-refl)
  open IsOrdEmbed
  open OrdStr
```

**定理** `≤` 反对称.  
**证明** 用序数的泛等原理改写 `≤-antisym-≃ₒ` 即证. ∎

```agda
≤-antisym : α ≤ β → β ≤ α → α ≡ β
≤-antisym α≤β β≤α = OrdPath _ _ ⁺¹ $ ≤-antisym-≃ₒ α≤β β≤α
```
    