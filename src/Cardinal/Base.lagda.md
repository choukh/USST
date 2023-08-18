---
title: 泛等结构集合论 (7) 直觉主义阿列夫层级
zhihu-tags: Agda, 同伦类型论（HoTT）, 集合论
---

# 泛等结构集合论 (7) 直觉主义阿列夫层级

> 交流Q群: 893531731  
> 本文源码: [Cardinal.Base.lagda.md](https://github.com/choukh/USST/blob/main/src/Cardinal/Base.lagda.md)  
> 高亮渲染: [Cardinal.Base.html](https://choukh.github.io/USST/Cardinal.Base.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification --hidden-argument-puns #-}

module Cardinal.Base where
open import Preliminary renaming (∣_∣₂ to ∣_∣)
open import Ordinal hiding (≤-refl; ≤-trans)
  renaming ( _≤_ to _≤ₒ_; ≤-prop to ≤ₒ-prop
           ; _<_ to _<ₒ_; <-prop to <ₒ-prop)
open BinaryRelation
```

## 基数

```agda
Card : (𝓊 : Level) → Type (𝓊 ⁺)
Card 𝓊 = ∥ hSet 𝓊 ∥₂
```

```agda
isSetCard : isSet (Card 𝓊)
isSetCard = squash₂
```

```agda
cardRec : (hSet 𝓊 → hProp (𝓊 ⁺)) → Card 𝓊 → hProp (𝓊 ⁺)
cardRec P = ∥∥₂-rec {B = hProp _} isSetHProp P
```

```agda
cardEqIso∥Eq∥ : {a b : hSet 𝓊} → Iso (∣ a ∣ ≡ ∣ b ∣) ∥ a ≡ b ∥₁
Iso.fun (cardEqIso∥Eq∥ {𝓊} {b}) p = subst (λ κ → cardRec (λ a → ∥ a ≡ b ∥ₚ) κ .fst) (sym p) ∣ refl ∣₁
Iso.inv       cardEqIso∥Eq∥ = ∥∥₁-rec (isSetCard _ _) (cong ∣_∣)
Iso.rightInv  cardEqIso∥Eq∥ _ = squash₁ _ _
Iso.leftInv   cardEqIso∥Eq∥ _ = isSetCard _ _ _ _
```

```agda
equivToCardEq : {a b : hSet 𝓊} → ⟨ a ⟩ ≃ ⟨ b ⟩ → ∣ a ∣ ≡ ∣ b ∣
equivToCardEq eqv = cong ∣_∣ $ Σ≡Prop (λ _ → isPropΠ2 λ _ _ → isPropIsProp) (ua eqv)
```

```agda
cardEqToEquip : {a b : hSet 𝓊} → ∣ a ∣ ≡ ∣ b ∣ → ⟨ a ⟩ ≈ ⟨ b ⟩
cardEqToEquip eq = ∥∥₁-map (λ x → subst (λ - → _ ≃ ⟨ - ⟩) x (idEquiv _)) (Iso.fun cardEqIso∥Eq∥ eq)
```

```agda
cardEqIsoEquip : {a b : hSet 𝓊} → Iso (∣ a ∣ ≡ ∣ b ∣) (⟨ a ⟩ ≈ ⟨ b ⟩)
Iso.fun       cardEqIsoEquip = cardEqToEquip
Iso.inv       cardEqIsoEquip = ∥∥₁-rec (isSetCard _ _) equivToCardEq
Iso.rightInv  cardEqIsoEquip _ = squash₁ _ _
Iso.leftInv   cardEqIsoEquip _ = isSetCard _ _ _ _
```

```agda
cardEq≃Equip : {a b : hSet 𝓊} → (∣ a ∣ ≡ ∣ b ∣) ≃ (⟨ a ⟩ ≈ ⟨ b ⟩)
cardEq≃Equip = isoToEquiv cardEqIsoEquip
```

## 基数的序

```agda
_≤ₕ_ : Card 𝓊 → Card 𝓋 → hProp (𝓊 ⊔ 𝓋)
_≤ₕ_ = ∥∥₂-rec2 isSetHProp λ (A , _) (B , _) → A ≲ B , squash₁
```

```agda
_≤_ : Card 𝓊 → Card 𝓋 → Type (𝓊 ⊔ 𝓋)
κ ≤ μ = ⟨ κ ≤ₕ μ ⟩

≤-prop : (κ : Card 𝓊) (μ : Card 𝓋) → isProp (κ ≤ μ)
≤-prop κ μ = str (κ ≤ₕ μ)

≤-set : (κ : Card 𝓊) (μ : Card 𝓋) → isSet (κ ≤ μ)
≤-set κ μ = isProp→isSet (≤-prop κ μ)
```

```agda
≤-refl : (κ : Card 𝓊) → κ ≤ κ
≤-refl = ∥∥₂-elim (λ _ → ≤-set _ _) λ _ → ∣ ↪-refl ∣₁
```

```agda
≤-trans : (κ : Card 𝓊) (μ : Card 𝓋) (ν : Card 𝓌) → κ ≤ μ → μ ≤ ν → κ ≤ ν
≤-trans = ∥∥₂-elim (λ _ → isSetΠ2 λ _ _ → isSet→ $ isSet→ $ ≤-set _ _)
  λ _ → ∥∥₂-elim2 (λ _ _ → isSet→ $ isSet→ $ ≤-set _ _) λ _ _ → ∥∥₁-map2 ↪-trans
```

```agda
∣⟨_⟩∣ : Ord 𝓊 → Card 𝓊
∣⟨ α ⟩∣ = ∣ ⟨ α ⟩ , ordSet ∣
```

```agda
<ₒ→≤ : α <ₒ β → ∣⟨ α ⟩∣ ≤ ∣⟨ β ⟩∣
<ₒ→≤ {β} (a , β↓a≡α) = subst (λ - → ∣⟨ - ⟩∣ ≤ ∣⟨ β ⟩∣) β↓a≡α ∣ ↑ , ↑-inj ∣₁
```

## 哈特格斯数

```agda
module Hartogs ⦃ _ : PR ⦄ {A : Type 𝓊} (Aset : isSet A) where

  ordCarrier : (𝓋 : Level) → Type (𝓊 ⊔ 𝓋 ⁺)
  ordCarrier 𝓋 = Σ α ∶ Ord 𝓋 , ⟨ α ⟩ ≲ A

  cardCarrier : Type (𝓊 ⁺)
  cardCarrier = Σ κ ∶ Card 𝓊 , κ ≤ ∣ A , Aset ∣

  isSetCardCarrier : isSet cardCarrier
  isSetCardCarrier = isSetΣ isSetCard λ _ → ≤-set _ _

  module Map {α : Ord 𝓋} ((f , f-inj) : ⟨ α ⟩ ↪ A) where
    hasPropFb : hasPropFibers f
    hasPropFb _ (a , p) (b , q) = Σ≡Prop (λ _ → Aset _ _) (f-inj $ p ∙ sym q)

    B : Type 𝓊
    B = Σ y ∶ A , ⟨ Resize {𝓋 = 𝓊} $ fiber f y , hasPropFb y ⟩

    Bset : isSet B
    Bset = isSetΣ Aset λ _ → isProp→isSet isPropResize

    B≤A : ∣ B , Bset ∣ ≤ ∣ A , Aset ∣
    B≤A = ∣ fst , Σ≡Prop (λ _ → isPropResize) ∣₁

  carrierMap : ordCarrier 𝓋 → cardCarrier
  carrierMap = uncurry λ α → elim→Set (λ _ → isSetCardCarrier) map 2const
    where
    map : ⟨ α ⟩ ↪ A → cardCarrier
    map f = ∣ B , Bset ∣ , B≤A
      where open Map f
    2const : (F G : ⟨ α ⟩ ↪ A) → map F ≡ map G
    2const F@(f , f-inj) G@(g , g-inj) =
      Σ≡Prop (λ _ → ≤-prop _ _) $ equivToCardEq $ h , h-equiv
      where
      open Map
      h : B F → B G
      h (y , p) = let (x , _) = fiber f y ∋ unresize p in g x , resize (x , refl)
      h-equiv : isEquiv h
      h-equiv = inj→sur→isEquiv (Bset G) inj sur
        where
        inj : injective h
        inj {y , p} {v , q} eq    with unresize p | unresize q | eq
        ... | (x , fx≡y) | _ | eq with unresize q | unresize p | eq
        ... | (u , fu≡v) | _ | eq = Σ≡Prop (λ _ → isPropResize) (sym fx≡y ∙ cong f x≡u ∙ fu≡v)
          where x≡u = g-inj $ cong fst eq
        sur : surjective h
        sur (y , p) with unresize p
        ... | (x , gx≡y) = ∣_∣₁ $ (g x , resize (x , {!   !})) , {!   !}
      i : Iso (B F) (B G)
      Iso.fun i (y , p) = let (x , _) = fiber f y ∋ unresize p in g x , resize (x , refl)
      Iso.inv i (y , p) = let (x , _) = fiber g y ∋ unresize p in f x , resize (x , refl)
      Iso.rightInv i (y , p) = Σ≡Prop (λ _ → isPropResize) {!   !}
        where
        H : fiber g y
        H = unresize p
      Iso.leftInv i = {!   !}
```
