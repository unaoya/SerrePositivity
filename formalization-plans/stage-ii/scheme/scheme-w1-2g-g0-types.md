# SC-W1 G0：型つきの宣言一覧

2026-11-14。新規六ファイルの宣言の型。定義については量化の形が界面なので定義式も示す。既存構成の法則や証明分割の本数を停止条件にはしない。200 行を超える宣言はない。

全ファイルの名前空間は `SerrePositivity.AlgebraicGeometry`。各節の `variable` 行はソースの共通文脈で、環の型クラスを省略して解釈しない。

## AffineVCover

ファイル全体：74 行。宣言数：7。

共通文脈：

```lean
universe u
```

### IsAffineVCover

```lean
def IsAffineVCover {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∀ (V : CommRingCat.{u}) [IsDomain V] [ValuationRing V] (k : A →+* V),
    ∃ (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ ∃ (e : V →+* W) (l : B →+* W),
        e.FaithfullyFlat ∧ l.comp f = e.comp k
```

### ValuativeCoverFamily

```lean
def ValuativeCoverFamily (rank : CommRingCat.{u} → Prop)
    {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ∀ (V : CommRingCat.{u}) [IsDomain V] [ValuationRing V], rank V → ∀ k : A →+* V,
    ∃ (i : ι) (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ rank W ∧ ∃ (e : V →+* W) (l : B i →+* W),
        e.FaithfullyFlat ∧ l.comp (f i) = e.comp k
```

### IsAffineVCoverFamily

```lean
def IsAffineVCoverFamily {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ValuativeCoverFamily (fun _ => True) B f

```

共通文脈の追加：`{A B C : Type u}`、`[CommRing A] [CommRing B] [CommRing C]`。

### isAffineVCover_of_retraction

```lean
theorem isAffineVCover_of_retraction (f : A →+* B) (r : B →+* A)
    (hr : r.comp f = RingHom.id A) : IsAffineVCover f
```

### isAffineVCover_id

```lean
theorem isAffineVCover_id : IsAffineVCover (RingHom.id A)
```

### IsAffineVCover.comp

```lean
theorem IsAffineVCover.comp {f : A →+* B} {g : B →+* C}
    (hg : IsAffineVCover g) (hf : IsAffineVCover f) : IsAffineVCover (g.comp f)
```

### IsAffineVCover.of_comp

```lean
theorem IsAffineVCover.of_comp {f : A →+* B} {g : B →+* C}
    (h : IsAffineVCover (g.comp f)) : IsAffineVCover f
```

## FiniteProductDomainFactor

ファイル全体：33 行。宣言数：1。

共通文脈：

```lean
universe u v w
```

### exists_factor_evalRingHom_of_isDomain

```lean
theorem exists_factor_evalRingHom_of_isDomain
    {ι : Type w} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    {V : Type v} [CommRing V] [IsDomain V] (f : (∀ i, B i) →+* V) :
    ∃ (i : ι) (l : B i →+* V), l.comp (Pi.evalRingHom B i) = f
```

## AffineVCoverFamily

ファイル全体：70 行。宣言数：4。

共通文脈：

```lean
universe u
variable {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
variable (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i)
```

### isAffineVCoverFamily_iff_pi

```lean
theorem isAffineVCoverFamily_iff_pi :
    IsAffineVCoverFamily B f ↔ IsAffineVCover (RingHom.pi f)
```

### isAffineVCoverFamily_of_member

```lean
theorem isAffineVCoverFamily_of_member (i : ι) (h : IsAffineVCover (f i)) :
    IsAffineVCoverFamily B f
```

### IsAffineVCoverFamily.of_refinement

```lean
theorem IsAffineVCoverFamily.of_refinement
    {κ : Type u} [Finite κ] (C : κ → Type u) [∀ j, CommRing (C j)]
    (g : ∀ j, A →+* C j) (ρ : κ → ι) (l : ∀ j, B (ρ j) →+* C j)
    (hl : ∀ j, (l j).comp (f (ρ j)) = g j) (h : IsAffineVCoverFamily C g) :
    IsAffineVCoverFamily B f
```

### IsAffineVCoverFamily.comp

```lean
theorem IsAffineVCoverFamily.comp (hf : IsAffineVCoverFamily B f)
    {κ : ι → Type u} [∀ i, Finite (κ i)]
    (C : ∀ i, κ i → Type u) [∀ i j, CommRing (C i j)]
    (g : ∀ i j, B i →+* C i j) (hg : ∀ i, IsAffineVCoverFamily (C i) (g i)) :
    IsAffineVCoverFamily (fun ij : Sigma κ ↦ C ij.1 ij.2)
      (fun ij ↦ (g ij.1 ij.2).comp (f ij.1))
```

## AffineVCoverBaseChange

ファイル全体：36 行。宣言数：1。

共通文脈：

```lean
universe u
variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
```

### IsAffineVCover.baseChange

```lean
theorem IsAffineVCover.baseChange
    {f : A →+* B} (α : A →+* C) (g : B →+* D) (β : C →+* D)
    (H : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom α)
      (CommRingCat.ofHom g) (CommRingCat.ofHom β))
    (hf : IsAffineVCover f) : IsAffineVCover β
```

## AffineVCoverSpectrum

ファイル全体：53 行。宣言数：4。

共通文脈：

```lean
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
```

### IsAffineVCover.surjectiveSpectrum

```lean
theorem IsAffineVCover.surjectiveSpectrum {f : A →+* B} (hf : IsAffineVCover f) :
    Function.Surjective (PrimeSpectrum.comap f)
```

### isAffineVCover_of_subsingleton

```lean
theorem isAffineVCover_of_subsingleton [Subsingleton A] (f : A →+* B) : IsAffineVCover f
```

### isAffineVCoverFamily_of_subsingleton

```lean
theorem isAffineVCoverFamily_of_subsingleton [Subsingleton A]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    (f : ∀ i, A →+* B i) : IsAffineVCoverFamily B f
```

### IsAffineVCoverFamily.nonempty

```lean
theorem IsAffineVCoverFamily.nonempty [Nontrivial A]
    {ι : Type u} [Finite ι] {B : ι → Type u} [∀ i, CommRing (B i)]
    {f : ∀ i, A →+* B i} (hf : IsAffineVCoverFamily B f) : Nonempty ι
```

## AffineVCoverFamilyBaseChange

ファイル全体：48 行。宣言数：2。

共通文脈：

```lean
universe u
variable {A C : Type u} [CommRing A] [CommRing C]
variable {ι : Type u} [Finite ι]
variable (B D : ι → Type u) [∀ i, CommRing (B i)] [∀ i, CommRing (D i)]
variable (f : ∀ i, A →+* B i) (α : A →+* C)
variable (g : ∀ i, B i →+* D i) (β : ∀ i, C →+* D i)
```

### IsAffineVCoverFamily.baseChange

```lean
theorem IsAffineVCoverFamily.baseChange
    (H : ∀ i, IsPushout (CommRingCat.ofHom (f i)) (CommRingCat.ofHom α)
      (CommRingCat.ofHom (g i)) (CommRingCat.ofHom (β i)))
    (hf : IsAffineVCoverFamily B f) : IsAffineVCoverFamily D β
```

### isAffineVCoverFamily_punit_iff

```lean
theorem isAffineVCoverFamily_punit_iff {E : Type u} [CommRing E] (h : A →+* E) :
    IsAffineVCoverFamily (fun _ : PUnit.{u + 1} ↦ E) (fun _ ↦ h) ↔ IsAffineVCover h
```


## 2026-11-14：付値持ち上げの追加束（検証済み）

数学 `5fb95d17b`・`d902118ed`。以下は各新規ファイルの共通文脈と宣言の型。

### ValuationProbeExtension

41 行。共通文脈：

```lean
universe u
variable {V R K : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable [CommRing R] [IsLocalRing R] [Field K]
```

`exists_valuationSubring_factor_of_injective_local_base`

```lean
theorem exists_valuationSubring_factor_of_injective_local_base
    (a : V →+* R) [IsLocalHom a] (f : R →+* K)
    (ha : Function.Injective (f.comp a)) :
    ∃ (W : ValuationSubring K) (b : R →+* W),
      IsLocalHom b ∧ (algebraMap W K).comp b = f ∧ (b.comp a).FaithfullyFlat
```

`exists_valuationSubring_extension_of_injective`

```lean
theorem exists_valuationSubring_extension_of_injective (i : V →+* K)
    (hi : Function.Injective i) :
    ∃ (W : ValuationSubring K) (e : V →+* W),
      (algebraMap W K).comp e = i ∧ e.FaithfullyFlat
```

### AffineVCoverNilImmersion

37 行。共通文脈：

```lean
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
```

`isAffineVCover_of_surjective_of_nil_kernel`

```lean
theorem isAffineVCover_of_surjective_of_nil_kernel (f : A →+* B)
    (hf : Function.Surjective f) (hn : RingHom.ker f ≤ nilradical A) : IsAffineVCover f
```

`isAffineVCover_quotient_of_le_nilradical`

```lean
theorem isAffineVCover_quotient_of_le_nilradical (J : Ideal A) (hJ : J ≤ nilradical A) :
    IsAffineVCover (Ideal.Quotient.mk J)
```

### FaithfullyFlatValuationLift

64 行。共通文脈：

```lean
universe u
variable {V B : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing B]
```

`exists_valuation_lift_of_faithfullyFlat`

```lean
theorem exists_valuation_lift_of_faithfullyFlat (f : V →+* B) (hf : f.FaithfullyFlat) :
    ∃ (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W
```

### AffineVCoverFaithfullyFlat

38 行。共通文脈：

```lean
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
```

`isAffineVCover_of_faithfullyFlat`

```lean
theorem isAffineVCover_of_faithfullyFlat (f : A →+* B) (hf : f.FaithfullyFlat) :
    IsAffineVCover f
```

### SchemeVCover

47 行。共通文脈：

```lean
universe u
```

`IsSchemeVCover`

```lean
def IsSchemeVCover {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (V : CommRingCat.{u}) [IsDomain V] [ValuationRing V] (k : Spec V ⟶ Y),
    ∃ (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ ∃ (e : V →+* W) (l : Spec W ⟶ X),
        e.FaithfullyFlat ∧ l ≫ f = Spec.map (CommRingCat.ofHom e) ≫ k
```

`isSchemeVCover_specMap_iff`

```lean
theorem isSchemeVCover_specMap_iff {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    IsSchemeVCover (Spec.map (CommRingCat.ofHom f)) ↔ IsAffineVCover f
```

### SchemeVCoverProper

58 行。共通文脈：

```lean
universe u
```

`isSchemeVCover_of_proper_surjective`

```lean
theorem isSchemeVCover_of_proper_surjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [Surjective f] : IsSchemeVCover f
```

### SchemeVCoverComposition

50 行。共通文脈：

```lean
universe u
variable {X Y Z : Scheme.{u}}
```

`IsSchemeVCover.comp`

```lean
theorem IsSchemeVCover.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsSchemeVCover f) (hg : IsSchemeVCover g) : IsSchemeVCover (f ≫ g)
```

`IsSchemeVCover.of_comp`

```lean
theorem IsSchemeVCover.of_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : IsSchemeVCover (f ≫ g)) : IsSchemeVCover g
```

`IsSchemeVCover.baseChange`

```lean
theorem IsSchemeVCover.baseChange {X' Y' : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (H : IsPullback a b f g) (hf : IsSchemeVCover f) : IsSchemeVCover b
```

### SchemeVCoverSurjective

33 行。共通文脈：

```lean
universe u
```

`IsSchemeVCover.surjective`

```lean
theorem IsSchemeVCover.surjective {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsSchemeVCover f) : Surjective f
```
