---
title: 泛等结构集合论 (7) 基数
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
---

# 泛等结构集合论 (7) 基数

> 交流Q群: 893531731  
> 本文源码: [Cardinal.Base.lagda.md](https://github.com/choukh/USST/blob/main/src/Cardinal/Base.lagda.md)  
> 高亮渲染: [Cardinal.Base.html](https://choukh.github.io/USST/Cardinal.Base.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --hidden-argument-puns #-}

module Cardinal.Base where
open import Preliminary
open import Ordinal renaming ( _≤_ to _≤ₒ_; ≤-prop to ≤ₒ-prop
                             ; _<_ to _<ₒ_; <-prop to <ₒ-prop)
```

## 基数

```agda
Card : (𝓊 : Level) → Type (𝓊 ⁺)
Card 𝓊 = ∥ hSet 𝓊 ∥₂
```

```agda
_≤ₕ_ : Card 𝓊 → Card 𝓋 → hProp (𝓊 ⊔ 𝓋)
_≤ₕ_ = ∥∥₂-rec2 isSetHProp λ (A , _) (B , _) → ∥ A ↪ B ∥₁ , squash₁
```

```agda
_≤_ : Card 𝓊 → Card 𝓋 → Type (𝓊 ⊔ 𝓋)
κ ≤ μ = ⟨ κ ≤ₕ μ ⟩

≤-prop : (κ : Card 𝓊) (μ : Card 𝓋) → isProp (κ ≤ μ)
≤-prop κ μ = str (κ ≤ₕ μ)
```

## 哈特格斯数

```agda
module PredicativeHartogs {A : Type 𝓊} (A-set : isSet A) where

  hartogs : EmbedOrd (𝓊 ⁺) (𝓊 ⁺)
  EmbedOrd.carrier       hartogs = Σ (B , strB) ∶ Ord 𝓊 , ∣ B , OrdStr.underlying-set strB ∣₂ ≤ ∣ A , A-set ∣₂
  EmbedOrd._≺_           hartogs (α , _) (β , _) = α <ₒ β
  EmbedOrd.relation-prop hartogs _ _ = <ₒ-prop _ _
  EmbedOrd.target        hartogs = Ω
  EmbedOrd.embed         hartogs = fst
  EmbedOrd.inj           hartogs = Σ≡Prop λ _ → ≤-prop _ _
  EmbedOrd.pres≺         hartogs _ _ = idfun _
  EmbedOrd.formsInitSeg  hartogs β (α′ , le) β<ₒα′ = (β , ∥∥₁-map H le) , β<ₒα′ , refl where
    H : ⟨ α′ ⟩ ↪ A → Σ (⟨ β ⟩ → A) injective
    H (f , f-inj) = f ∘ g , g-inj ∘ f-inj where
      g = <→≤ β<ₒα′ .fst
      g-inj = IsOrdEmbed.inj $ <→≤ β<ₒα′ .snd
```

```agda
  ℍ : Ord (𝓊 ⁺)
  ℍ = tieup hartogs
```

```agda
  ℍ→ℙ³ : ⟨ ℍ ⟩ → ℙ (ℙ (ℙ A))
  ℍ→ℙ³ (β , _) X = Lift ∥ Iso Sub ⟨ β ⟩ ∥₁ , isOfHLevelLift 1 squash₁
    where Sub = Σ (x , _) ∶ ⟦ X ⟧ , Σ (y , _) ∶ ⟦ X ⟧ , x ⊂ y
```

  ℍ→ℙ³-inj : injective ℍ→ℙ³
  ℍ→ℙ³-inj = {!   !}

  resizeCarrier : ⦃ _ : PR ⦄ → Type (𝓊 ⁺)
  resizeCarrier = Σ x ∶ ⟨ ℍ ⟩ , Σ y ∶ ℙ[ 𝓊 ][ 2 ]⁺ A , {!ℍ→ℙ³ x   !} ≡ y

回想我们有: 假设 `PR`, 可以将任意 `β : Ord 𝓋` 降级到 `Ord 𝓊` 上, 只要找到一个 `A : Type 𝓊` 满足 `A ≃ ⟨ β ⟩`.

```agda
  _ : ⦃ _ : PR ⦄ (A : Type 𝓊) (β : Ord 𝓋) → A ≃ ⟨ β ⟩ → Ord 𝓊
  _ = ResizeOrd
```

## 超限归纳与超限递归

`Ω` 底序的良基消去规则 `elim` 是超限归纳和超限递归的一般形式, 稍微整形一下就可以得到超限归纳 `ind` 和超限递归 `rec`.

```agda
ind : {P : Ord 𝓊 → Type 𝓋} → (∀ α → (∀ a → P (α ↓ a)) → P α) → ∀ α → P α
ind {P} IH = OrdStr.elim (str Ω) IH′ where
  IH′ : ∀ α → (∀ β → β <ₒ α → P β) → P α
  IH′ α H = IH α λ a → H (α ↓ a) (a , refl)

rec : {A : Type 𝓋} → ((α : Ord 𝓊) → (⟨ α ⟩ → A) → A) → Ord 𝓊 → A
rec = ind
```

```agda
ind-compute : {P : Ord 𝓊 → Type 𝓋} (H : ∀ α → (∀ a → P (α ↓ a)) → P α)
  (α : Ord 𝓊) → ind H α ≡ H α (λ a → ind H (α ↓ a))
ind-compute {P} IH = OrdStr.compute (str Ω) IH′ where
  IH′ : ∀ α → (∀ β → β <ₒ α → P β) → P α
  IH′ α H = IH α λ a → H (α ↓ a) (a , refl)

rec-compute : {A : Type 𝓋} (f : (α : Ord 𝓊) → (⟨ α ⟩ → A) → A)
  (α : Ord 𝓊) → rec f α ≡ f α λ a → rec f (α ↓ a)
rec-compute = ind-compute
```

```agda
Rec : {A : Type 𝓋} (f : (α : Ord 𝓊) → (⟨ α ⟩ → A) → A) →
  Σ g ∶ (Ord 𝓊 → A) , ∀ α → g α ≡ f α λ a → g (α ↓ a)
Rec f = rec f , rec-compute f
```