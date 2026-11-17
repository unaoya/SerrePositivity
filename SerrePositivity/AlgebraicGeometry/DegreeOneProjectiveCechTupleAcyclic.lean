module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquare
public import SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModelPerfectSquare
public import SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModelFiberPowers
public import SerrePositivity.AlgebraicGeometry.FiniteFiberPowerGeometricInputs
public import SerrePositivity.AlgebraicGeometry.CechNerveCartesianBaseChange
public import SerrePositivity.AlgebraicGeometry.SchemeCechTupleAffine

/-!
概要：同じ射影表示と閉中心を保ち、実際の nerve の各項へ F8 を適用する。
方針：既存の有限冪の表示と幾何学的入力、同じタプル被覆の比較を使う。
規約：元の R/I^1 と実際の係数・スカラー・制限を保持する。
使われ方：同じ四角形の可換な二重 Čech に渡す列の完全性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
variable {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of (R ⧸ I ^ 1)))
variable (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g)
variable (hq : F.right = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1))))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ nerve の各項で、実際のタプル被覆の四角形の全複体は完全。
BST13 Lemma 3.9・BS17 Lemma 4.6(i) に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem DegreeOneProjectiveModel.perfectCechTupleSquare_acyclic
    (m : DegreeOneProjectiveModel g) (H : IsPullback F.left f g F.right)
    [Surjective g] [IsIso (g ∣_ affineCenterComplement I)]
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) (n : SimplexCategory) :
    (schemePerfectCechTupleSquare f g F (Ideal.Quotient.mk (I ^ 1)) hq U p hp hR
      (frobeniusQuotientPrimeCast p hR (I ^ 1)) n).totalComplex.Acyclic := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  have : Surjective ((Arrow.mk g).augmentedCechNerve.hom.app (op n)) :=
    finiteFiberPowerBase_surjective g n.len
  have : IsIso ((Arrow.mk g).augmentedCechNerve.hom.app (op n) ∣_
      affineCenterComplement I) :=
    finiteFiberPowerBase_restrict_isIso g (affineCenterComplement I) n.len
  have H' : IsPullback ((Arrow.mapCechNerve F).app (op n))
      ((Arrow.mk f).augmentedCechNerve.hom.app (op n))
      ((Arrow.mk g).augmentedCechNerve.hom.app (op n))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1)))) := by
    change IsPullback ((Arrow.mapCechNerve F).app (op n))
      (WidePullback.base (fun _ : Fin (n.len + 1) ↦ f))
      (WidePullback.base (fun _ : Fin (n.len + 1) ↦ g)) _
    exact hq ▸ isPullback_cechNerve_base F H (op n)
  have ha := (m.cechTerm (op n)).perfectCartesianSquare_acyclic I
    ((Arrow.mapCechNerve F).app (op n)) ((Arrow.mk f).augmentedCechNerve.hom.app (op n)) H'
    p hp hR (schemeCechTupleOpen g U (op n))
    (fun t ↦ schemeCechTupleOpen_isAffine g U hU n.len t)
    (schemeCechTupleOpen_iSup g U hcU (op n))
  exact (schemeStructurePerfectCechRefinedSquare_acyclic_iff_of_eq
    ((Arrow.mapCechNerve F).app (op n)) (Ideal.Quotient.mk (I ^ 1))
    (schemeScalarHom _ ((Arrow.mk g).augmentedCechNerve.hom.app (op n)))
    (schemeScalarHom _ ((Arrow.mk f).augmentedCechNerve.hom.app (op n)))
    (schemeCechNerveMapScalarHom_naturality f g F (Ideal.Quotient.mk (I ^ 1)) hq (op n))
    p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
    (schemeCechNervePresheaf_primeCast g p hR (op n))
    (schemeCechNervePresheaf_primeCast f p (frobeniusQuotientPrimeCast p hR (I ^ 1)) (op n))
    (schemeCechTupleOpen g U (op n))
    (schemeCechTupleOpen f (fun i ↦ F.left ⁻¹ᵁ U i) (op n))
    (fun t ↦ le_of_eq (schemeCechTupleOpen_mapCechNerve_preimage F U (op n) t))
    (funext (fun t ↦ schemeCechTupleOpen_mapCechNerve_preimage F U (op n) t))).mp ha

end SerrePositivity.AlgebraicGeometry
