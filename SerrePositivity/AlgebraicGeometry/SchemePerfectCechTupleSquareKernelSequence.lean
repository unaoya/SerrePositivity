module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquareBaseComparison
public import SerrePositivity.AlgebraicGeometry.CechShortComplexKernelExact

/-!
概要：実際のF8と基底列の比較から、同じ核の短完全列を得る。
方針：三つの全射と既存のsnake lemma・totalの短完全性を使う。
規約：中項は元の実際の射影の核と比較し、元の包含を保つ。
使われ方：中心側の帰納仮定からY側へ戻す条件付きのČech版の消去。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
local notation "up" => ComplexShape.up ℕ
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

/-- 元の実際の三つの射影の同じ核の列。 -/
def schemePerfectCechTupleSquareKernelSequence :
    ShortComplex (HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) :=
  kernel (schemePerfectCechTupleSquareBaseComparison f g F q hq U p hp hR hS)

set_option backward.isDefEq.respectTransparency false in
/-- 元の実際の比較の射は全成分全射で、同じ核の列は短完全。 -/
theorem schemePerfectCechTupleSquareKernelSequence_shortExact :
    (schemePerfectCechTupleSquareKernelSequence f g F q hq U p hp hR hS).ShortExact := by
  let A := schemePerfectCechTupleSquarePositiveLeftRightShortComplex f g F q hq U p hp hR hS
  let B := schemePerfectCechTupleSquareBaseLeftRightShortComplex f g F q hq U p hp hR hS
  let φ : A ⟶ B := schemePerfectCechTupleSquareBaseComparison f g F q hq U p hp hR hS
  letI : Epi φ.τ₁ := HomologicalComplex.epi_of_epi_f _ (fun n ↦
    HomologicalComplex.epi_of_epi_f _ (fun b ↦ (ModuleCat.epi_iff_surjective _).mpr
      (schemePerfectCechTupleSquarePositiveBaseRightProjection_surjective
        f g F q hq U p hp hR hS n b)))
  letI : Epi φ.τ₂ := HomologicalComplex.epi_of_epi_f _ (fun n ↦
    HomologicalComplex.epi_of_epi_f _ (fun b ↦ (ModuleCat.epi_iff_surjective _).mpr
      (schemePerfectCechTupleSquarePositiveBaseProjection_surjective
        f g F q hq U p hp hR hS n b)))
  letI : Epi φ.τ₃ := HomologicalComplex.epi_of_epi_f _ (fun n ↦
    HomologicalComplex.epi_of_epi_f _ (fun b ↦ (ModuleCat.epi_iff_surjective _).mpr
      (schemePerfectCechTupleSquarePositiveBaseLeftProjection_surjective
        f g F q hq U p hp hR hS n b)))
  letI : Epi φ := ⟨by
    intro Z a b hab
    apply ShortComplex.hom_ext
    · exact (cancel_epi φ.τ₁).mp (congrArg ShortComplex.Hom.τ₁ hab)
    · exact (cancel_epi φ.τ₂).mp (congrArg ShortComplex.Hom.τ₂ hab)
    · exact (cancel_epi φ.τ₃).mp (congrArg ShortComplex.Hom.τ₃ hab)⟩
  exact cechShortComplexKernel_shortExact (C := HomologicalComplex₂ (ModuleCat.{u} ℤ) up up)
    (S := A) (T := B) φ
    (schemePerfectCechTupleSquarePositiveLeftRight_shortExact f g F q hq U p hp hR hS)
    (schemePerfectCechTupleSquareBaseLeftRight_shortExact f g F q hq U p hp hR hS)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ核の列の中項は、元の実際の中央の射影の核。 -/
def schemePerfectCechTupleSquareKernelSequenceMiddleIso :
    (schemePerfectCechTupleSquareKernelSequence f g F q hq U p hp hR hS).X₂ ≅
      schemePerfectCechTupleSquareReducedDouble f g F q hq U p hp hR hS := by
  let e := cechShortComplexKernelMiddleIso (C := HomologicalComplex₂ (ModuleCat.{u} ℤ) up up)
    (S := schemePerfectCechTupleSquarePositiveLeftRightShortComplex f g F q hq U p hp hR hS)
    (T := schemePerfectCechTupleSquareBaseLeftRightShortComplex f g F q hq U p hp hR hS)
    (schemePerfectCechTupleSquareBaseComparison f g F q hq U p hp hR hS)
  exact e

set_option backward.isDefEq.respectTransparency false in
/-- 中項の同じ標準比較は元の実際の核の包含を保つ。 -/
theorem schemePerfectCechTupleSquareKernelSequenceMiddleIso_hom_ι :
    (schemePerfectCechTupleSquareKernelSequenceMiddleIso f g F q hq U p hp hR hS).hom ≫
        kernel.ι (schemePerfectCechTupleSquarePositiveBaseProjection f g F q hq U p hp hR hS) =
      (kernel.ι (schemePerfectCechTupleSquareBaseComparison f g F q hq U p hp hR hS)).τ₂ := by
  let e := cechShortComplexKernelMiddleIso_hom_ι (C := HomologicalComplex₂ (ModuleCat.{u} ℤ) up up)
    (S := schemePerfectCechTupleSquarePositiveLeftRightShortComplex f g F q hq U p hp hR hS)
    (T := schemePerfectCechTupleSquareBaseLeftRightShortComplex f g F q hq U p hp hR hS)
    (schemePerfectCechTupleSquareBaseComparison f g F q hq U p hp hR hS)
  exact e

/-- 元の実際の中心側の射影の同じ核に、二重複体の型を明示する。 -/
def schemePerfectCechTupleSquareRightKernel : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
  kernel (schemePerfectCechTupleSquarePositiveBaseRightProjection f g F q hq U p hp hR hS)

/-- 元の実際のY側の射影の同じ核に、二重複体の型を明示する。 -/
def schemePerfectCechTupleSquareLeftKernel : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
  kernel (schemePerfectCechTupleSquarePositiveBaseLeftProjection f g F q hq U p hp hR hS)

variable [IsNoetherianRing R] (I : Ideal R)
variable (fI : X ⟶ Spec (CommRingCat.of (R ⧸ I ^ 1)))
variable (FI : Arrow.mk fI ⟶ Arrow.mk g)
variable (hqI : FI.right = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1))))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ中心側の核のtotalの完全性からY側へ戻す、条件付きのČech版の消去。
BST13 Lemma 3.9・BS17 Lemma 4.6(i) の射影F8を用いる。
分離的なスキームの準連接層ではアフィン被覆のČechと一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem DegreeOneProjectiveModel.perfectCechTupleSquareLeftKernelTotal_acyclic_of_right
    (m : DegreeOneProjectiveModel g) (H : IsPullback FI.left fI g FI.right)
    [Surjective g] [IsIso (g ∣_ affineCenterComplement I)]
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤)
    (hRight : (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleSquareRightKernel fI g FI
        (Ideal.Quotient.mk (I ^ 1)) hqI U p hp hR
          (frobeniusQuotientPrimeCast p hR (I ^ 1))) up).Acyclic) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleSquareLeftKernel fI g FI
        (Ideal.Quotient.mk (I ^ 1)) hqI U p hp hR
          (frobeniusQuotientPrimeCast p hR (I ^ 1))) up).Acyclic := by
  let A := schemePerfectCechTupleSquarePositiveLeftRightShortComplex fI g FI
    (Ideal.Quotient.mk (I ^ 1)) hqI U p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
  let B := schemePerfectCechTupleSquareBaseLeftRightShortComplex fI g FI
    (Ideal.Quotient.mk (I ^ 1)) hqI U p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
  let φ : A ⟶ B := schemePerfectCechTupleSquareBaseComparison fI g FI (Ideal.Quotient.mk (I ^ 1))
    hqI U p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
  let D := schemePerfectCechTupleSquareKernelSequence fI g FI (Ideal.Quotient.mk (I ^ 1))
    hqI U p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
  have hs := cechIntegerLiftTotal_shortExact D
    (schemePerfectCechTupleSquareKernelSequence_shortExact fI g FI (Ideal.Quotient.mk (I ^ 1))
      hqI U p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1)))
  have ho := DegreeOneProjectiveModel.perfectCechTupleSquareReducedTotal_acyclic
    (g := g) (U := U) (p := p) (hp := hp) (hR := hR) (I := I) (fI := fI)
    (FI := FI) (hqI := hqI) m H hU hcU
  let eM := cechShortComplexKernelMiddleIso
    (C := HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) (S := A) (T := B) φ
  let eR := cechShortComplexKernelLeftIso
    (C := HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) (S := A) (T := B) φ
  let eL := cechShortComplexKernelRightIso
    (C := HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) (S := A) (T := B) φ
  let eMt := HomologicalComplex₂.total.mapIso eM up
  let eRt := HomologicalComplex₂.total.mapIso eR up
  let eLt := HomologicalComplex₂.total.mapIso eL up
  have hm : (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ) D.X₂ up).Acyclic := fun n ↦
    (ho n).of_iso eMt.symm
  have hr : (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ) D.X₁ up).Acyclic := fun n ↦
    (hRight n).of_iso eRt.symm
  have hl : (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ) D.X₃ up).Acyclic := by
    apply hs.acyclic_X₃
    constructor
    intro n
    exact (_root_.quasiIsoAt_iff_exactAt _ n (hr n)).mpr (hm n)
  intro n
  exact (hl n).of_iso eLt

end SerrePositivity.AlgebraicGeometry
