module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleRightKernelTotal
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleLeftTotalShortComplex

/-!
概要：元の中心の完全性を、同じF8と元の核の比較を通じて元の増大totalへ戻す。
方針：右側の同じ核、F8の消去、左側の同じ核の比較の三つを合成する。
規約：中心の完全性を入力とする補題であり、一般の固有降下の完成とは主張しない。
使われ方：Noether閉像帰納での射影的な段の実際の出口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
local notation "up" => ComplexShape.up ℕ
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X Y : Scheme.{u}}
variable (g : Y ⟶ Spec (CommRingCat.of R)) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (I : Ideal R)
variable (fI : X ⟶ Spec (CommRingCat.of (R ⧸ I ^ 1))) (FI : Arrow.mk fI ⟶ Arrow.mk g)
variable (hqI : FI.right = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1))))

set_option backward.isDefEq.respectTransparency false in
include hqI in
/-- 元の中心の増大totalの完全性から、同じ元の射影的F8の増大totalへ戻すČech版。
BST13 Lemma 3.9・BS17 Lemma 4.6(i)の射影Čech版を使う。
分離的なスキームの準連接層ではアフィン被覆のČechと一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem DegreeOneProjectiveModel.perfectCechTupleTotal_acyclic_of_center
    (m : DegreeOneProjectiveModel g) (H : IsPullback FI.left fI g FI.right)
    [Surjective g] [IsIso (g ∣_ affineCenterComplement I)]
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤)
    (hCenter : (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble fI (fun i ↦ FI.left ⁻¹ᵁ U i) p hp
        (frobeniusQuotientPrimeCast p hR (I ^ 1))) up).Acyclic) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (schemePerfectCechTupleDouble g U p hp hR) up).Acyclic := by
  have hr := schemePerfectCechTupleRightKernelTotal_acyclic_of_center fI g FI
    (Ideal.Quotient.mk (I ^ 1)) hqI U p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1)) hCenter
  have hl := DegreeOneProjectiveModel.perfectCechTupleSquareLeftKernelTotal_acyclic_of_right
    (g := g) (U := U) (p := p) (hp := hp) (hR := hR) (I := I) (fI := fI) (FI := FI) (hqI := hqI)
    m H hU hcU hr
  exact (schemePerfectCechTupleLeftKernelTotal_acyclic_iff fI g FI
    (Ideal.Quotient.mk (I ^ 1)) hqI U p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))).mp hl

end SerrePositivity.AlgebraicGeometry
