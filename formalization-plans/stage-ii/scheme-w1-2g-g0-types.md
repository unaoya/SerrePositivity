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
