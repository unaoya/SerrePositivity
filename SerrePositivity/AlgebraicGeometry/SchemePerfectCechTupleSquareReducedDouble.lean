module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquareBaseProjection
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquarePositiveTotal
public import SerrePositivity.AlgebraicGeometry.CechConstantPositiveDoubleTotal
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalShortExact
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
概要：実際のF8の全複体から余分な定数基底列を除く。
方針：同じ射影の核の短完全性と既存の全複体の短完全性を使う。
規約：元の各F8の項・射と基底・中心の係数を保つČech版。
使われ方：中心側との有限cone比較と元の閉像のNoether帰納。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology
universe u
local notation "up" => ComplexShape.up ℕ
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 実際のF8図式を同じ定数基底列の正次数の商へ送る。 -/
def schemePerfectCechTupleSquarePositiveBaseProjection :
    schemePerfectCechTupleSquarePositiveDouble f g F q hq U p hp hR hS ⟶
      cechConstantPositiveDouble
        (schemePerfectCechTupleSquareBaseComplex f g F q hq U p hp hR hS) :=
  (alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).map
      (schemePerfectCechTupleSquareBaseProjection f g F q hq U p hp hR hS) ≫
    cechConstantPositiveDoubleProjection
      (schemePerfectCechTupleSquareBaseComplex f g F q hq U p hp hR hS)

set_option backward.isDefEq.respectTransparency false in
/-- 元の射影の全ての外次数・縦次数の成分は全射。 -/
theorem schemePerfectCechTupleSquarePositiveBaseProjection_surjective (n b : ℕ) :
    Function.Surjective
      (((schemePerfectCechTupleSquarePositiveBaseProjection f g F q hq U p hp hR hS).f n).f b).hom :=
  (cechConstantPositiveDoubleProjection_surjective
    (schemePerfectCechTupleSquareBaseComplex f g F q hq U p hp hR hS) n b).comp
      (schemePerfectCechTupleSquareBaseProjection_surjective f g F q hq U p hp hR hS
        (SimplexCategory.mk n) b)

/-- 実際の同じ射影の核を取り、外正次数の余分な基底項を除く。 -/
def schemePerfectCechTupleSquareReducedDouble :
    HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
  kernel (schemePerfectCechTupleSquarePositiveBaseProjection f g F q hq U p hp hR hS)

/-- 同じ射影の核からなる既存の短複体。 -/
def schemePerfectCechTupleSquareReducedShortComplex :
    ShortComplex (HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) :=
  ShortComplex.mk
    (kernel.ι (schemePerfectCechTupleSquarePositiveBaseProjection f g F q hq U p hp hR hS))
    (schemePerfectCechTupleSquarePositiveBaseProjection f g F q hq U p hp hR hS)
    (kernel.condition _)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ全成分全射の射影の核の短複体は短完全。 -/
theorem schemePerfectCechTupleSquareReduced_shortExact :
    (schemePerfectCechTupleSquareReducedShortComplex f g F q hq U p hp hR hS).ShortExact := by
  let P := schemePerfectCechTupleSquarePositiveBaseProjection f g F q hq U p hp hR hS
  let T := schemePerfectCechTupleSquareReducedShortComplex f g F q hq U p hp hR hS
  letI : Abelian (HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) :=
    inferInstanceAs (Abelian (CochainComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) ℕ))
  letI : T.HasHomology := inferInstance
  letI : Epi P := HomologicalComplex.epi_of_epi_f P (fun n ↦
    HomologicalComplex.epi_of_epi_f _ (fun b ↦ (ModuleCat.epi_iff_surjective _).mpr
      (schemePerfectCechTupleSquarePositiveBaseProjection_surjective
        f g F q hq U p hp hR hS n b)))
  exact { exact := ShortComplex.exact_of_f_is_kernel T (kernelIsKernel P)
          mono_f := inferInstanceAs (Mono (kernel.ι P))
          epi_g := inferInstanceAs (Epi P) }

variable [IsNoetherianRing R] (I : Ideal R)
variable (fI : X ⟶ Spec (CommRingCat.of (R ⧸ I ^ 1)))
variable (FI : Arrow.mk fI ⟶ Arrow.mk g)
variable (hqI : FI.right = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1))))

set_option backward.isDefEq.respectTransparency false in
/-- 元の射影F8の完全性は、同じ余分な定数基底列を除いても保たれるČech版。
BST13 Lemma 3.9・BS17 Lemma 4.6(i) の射影Čech四角形を用いる。
分離的なスキームの準連接層ではアフィン被覆のČechと一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem DegreeOneProjectiveModel.perfectCechTupleSquareReducedTotal_acyclic
    (m : DegreeOneProjectiveModel g) (H : IsPullback FI.left fI g FI.right)
    [Surjective g] [IsIso (g ∣_ affineCenterComplement I)]
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) :
    ((schemePerfectCechTupleSquareReducedDouble fI g FI (Ideal.Quotient.mk (I ^ 1))
      hqI U p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))).total up).Acyclic := by
  let T := schemePerfectCechTupleSquareReducedShortComplex fI g FI
    (Ideal.Quotient.mk (I ^ 1)) hqI U p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
  have ht := cechIntegerLiftTotal_shortExact T
    (schemePerfectCechTupleSquareReduced_shortExact fI g FI (Ideal.Quotient.mk (I ^ 1))
      hqI U p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1)))
  have hd := DegreeOneProjectiveModel.perfectCechTupleSquarePositiveTotal_acyclic
    (g := g) (U := U) (p := p) (hp := hp) (hR := hR) (I := I) (fI := fI)
    (FI := FI) (hqI := hqI) m H hU hcU
  have hq := cechConstantPositiveDouble_total_acyclic
    (schemePerfectCechTupleSquareBaseComplex fI g FI (Ideal.Quotient.mk (I ^ 1))
      hqI U p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1)))
  apply ht.acyclic_X₁
  constructor
  intro n
  exact (_root_.quasiIsoAt_iff_exactAt _ n (hd n)).mpr (hq n)

end SerrePositivity.AlgebraicGeometry
