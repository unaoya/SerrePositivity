module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectCartesianScalarSquare
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareComparison
public import SerrePositivity.AlgebraicGeometry.CechConeQuasiIsoAcyclic

/-!
概要：F8 の既存の完全な四角形から、同じ native なスカラーの四角形へ移す。
方針：二つの複体と基底・中心を固定した、実際の四角形の射で各辺を照合する。
規約：F8 の完全性を仮定にせず、検証済みの完全性を同じ射で移す。
使われ方：任意の有限アフィン被覆で F8 を使う入口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance scalarSquareComparisonGradedRing :
    GradedRing (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G 1
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]
variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ 1))) (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1)))))

set_option backward.isDefEq.respectTransparency false in
/-- F8 の scalar は、同じ Proj の大域スカラーの native な増大写像。 -/
theorem projectivePerfectCartesianScalarAugmentation_eq_native :
    (projectivePerfectCartesianAugmentedSquare
      (ι := ι) G I p hp hR hA hspan iY g H).scalar =
        schemeStructurePerfectCechAugmentation (Proj G) (projectiveScalarToGlobalSections G)
          p hp hR (projectiveProjPresheaf_primeCast G p hR) (projectiveProjCechOpen (ι := ι) G) := by
    apply LinearMap.ext
    intro x
    change FrobeniusDirectLimit R p hp hR at x
    funext t
    change Fin 1 → ι at t
    exact (projectivePerfectCartesianAugmentedSquare_scalar_apply G I p hp hR hA hspan
      iY g H x t).trans
        (schemeStructurePerfectCechAugmentation_apply (Proj G)
          (projectiveScalarToGlobalSections G) p hp hR
          (projectiveProjPresheaf_primeCast G p hR) (projectiveProjCechOpen (ι := ι) G) x t).symm

set_option backward.isDefEq.respectTransparency false in
/-- F8 の quotient は、同じ商の実際の Frobenius 順極限の写像。 -/
theorem projectivePerfectCartesianQuotient_eq_native :
    (projectivePerfectCartesianAugmentedSquare
      (ι := ι) G I p hp hR hA hspan iY g H).quotient =
        (frobeniusDirectLimitMap p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
          (Ideal.Quotient.mk (I ^ 1))).toAddMonoidHom.toIntLinearMap := rfl

set_option backward.isDefEq.respectTransparency false in
/-- F8 の center は、同じ閉中心の大域スカラーの native な増大写像。 -/
theorem projectivePerfectCartesianCenterAugmentation_eq_native :
    (projectivePerfectCartesianAugmentedSquare
      (ι := ι) G I p hp hR hA hspan iY g H).center =
        schemeStructurePerfectCechAugmentation Y (schemeScalarHom Y iY) p hp
          (frobeniusQuotientPrimeCast p hR (I ^ 1))
          (projectivePullbackPresheaf_primeCast G g p hR)
          (fun i ↦ g ⁻¹ᵁ projectiveProjCechOpen (ι := ι) G i) := by
    rw [projectivePerfectCartesianAugmentedSquare_center]
    dsimp only [projectivePerfectCartesianCenterAugmentation]
    let Q := frobeniusRingDiagram Y.presheaf p hp (projectivePullbackPresheaf_primeCast G g p hR)
    let U := projectiveProjCechOpen (ι := ι) G
    let b := (frobeniusDirectLimitMap p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))
      (projectivePullbackPresheaf_primeCast G g p hR (op ⊤))
      (schemeScalarHom Y iY)).toAddMonoidHom.toIntLinearMap
    change _ = (openCoverCechAugmentation Q (fun i ↦ g ⁻¹ᵁ U i)).comp b
    rw [← schemeCechPreimageComplexIso_augmentation g Q U, LinearMap.comp_assoc]
    congr 1
    apply LinearMap.ext
    intro x
    funext t
    exact (congrArg (fun m ↦ m x)
      (frobeniusDirectLimitMap_comp p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))
        (projectivePullbackPresheaf_primeCast G g p hR (op ⊤)) (schemeScalarHom Y iY)
        (projectivePullbackPresheaf_primeCast G g p hR _)
        (Y.presheaf.map (homOfLE (show
          g ⁻¹ᵁ cechOpenIntersection U (cechTupleSupport t) ≤ ⊤ from le_top)).op).hom)).symm

set_option backward.isDefEq.respectTransparency false in
/-- 既存の比較の射の restriction の自然性を、そのままの型で渡す。 -/
theorem projectivePerfectCartesianScalarMap_restriction :
    (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).restriction ≫ (𝟙 (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).E) =
      (𝟙 (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).C) ≫ (projectivePerfectCartesianScalarSquare G I iY g H p hp hR
      (projectiveProjCechOpen (ι := ι) G)).restriction := by
    change (projectivePerfectCartesianAugmentedSquare
      (ι := ι) G I p hp hR hA hspan iY g H).restriction ≫ (𝟙 _) =
        (𝟙 _) ≫ schemeStructurePerfectCechPullbackMap g p hp
          (projectiveProjPresheaf_primeCast G p hR) (projectivePullbackPresheaf_primeCast G g p hR)
          (projectiveProjCechOpen (ι := ι) G)
    simpa only [Category.comp_id, Category.id_comp] using
      projectivePerfectCartesianAugmentedSquare_restriction G I p hp hR hA hspan iY g H

set_option backward.isDefEq.respectTransparency false in
/-- 既存の比較の射の scalar の自然性を、そのままの型で渡す。 -/
theorem projectivePerfectCartesianScalarMap_scalar :
    LinearMap.id.comp (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).scalar =
      (projectivePerfectCartesianScalarSquare G I iY g H p hp hR
      (projectiveProjCechOpen (ι := ι) G)).scalar.comp LinearMap.id := by
    change (projectivePerfectCartesianAugmentedSquare
      (ι := ι) G I p hp hR hA hspan iY g H).scalar =
        schemeStructurePerfectCechAugmentation (Proj G) (projectiveScalarToGlobalSections G)
          p hp hR (projectiveProjPresheaf_primeCast G p hR) (projectiveProjCechOpen (ι := ι) G)
    exact projectivePerfectCartesianScalarAugmentation_eq_native G I p hp hR hA hspan iY g H

set_option backward.isDefEq.respectTransparency false in
/-- 既存の比較の射の quotient の自然性を、そのままの型で渡す。 -/
theorem projectivePerfectCartesianScalarMap_quotient :
    LinearMap.id.comp (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).quotient =
      (projectivePerfectCartesianScalarSquare G I iY g H p hp hR
      (projectiveProjCechOpen (ι := ι) G)).quotient.comp LinearMap.id := by
    change (projectivePerfectCartesianAugmentedSquare
      (ι := ι) G I p hp hR hA hspan iY g H).quotient =
        (frobeniusDirectLimitMap p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
          (Ideal.Quotient.mk (I ^ 1))).toAddMonoidHom.toIntLinearMap
    exact projectivePerfectCartesianQuotient_eq_native G I p hp hR hA hspan iY g H

set_option backward.isDefEq.respectTransparency false in
/-- 既存の比較の射の center の自然性を、そのままの型で渡す。 -/
theorem projectivePerfectCartesianScalarMap_center :
    LinearMap.id.comp (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).center =
      (projectivePerfectCartesianScalarSquare G I iY g H p hp hR
      (projectiveProjCechOpen (ι := ι) G)).center.comp LinearMap.id := by
    change (projectivePerfectCartesianAugmentedSquare
      (ι := ι) G I p hp hR hA hspan iY g H).center =
        schemeStructurePerfectCechAugmentation Y (schemeScalarHom Y iY) p hp
          (frobeniusQuotientPrimeCast p hR (I ^ 1))
          (projectivePullbackPresheaf_primeCast G g p hR)
          (fun i ↦ g ⁻¹ᵁ projectiveProjCechOpen (ι := ι) G i)
    exact projectivePerfectCartesianCenterAugmentation_eq_native G I p hp hR hA hspan iY g H

set_option backward.isDefEq.respectTransparency false in
/-- F8 の四角形から同じ複体・係数の native なスカラー四角形への実際の射。 -/
def projectivePerfectCartesianToScalarSquare :
    CechAugmentedSquare.Map
      (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H)
      (projectivePerfectCartesianScalarSquare G I iY g H p hp hR
        (projectiveProjCechOpen (ι := ι) G)) where
  left := 𝟙 (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).C
  right := 𝟙 (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).E
  base := LinearMap.id
  center := LinearMap.id
  restriction := projectivePerfectCartesianScalarMap_restriction G I p hp hR hA hspan iY g H
  scalar := projectivePerfectCartesianScalarMap_scalar G I p hp hR hA hspan iY g H
  quotient := projectivePerfectCartesianScalarMap_quotient G I p hp hR hA hspan iY g H
  center_naturality := projectivePerfectCartesianScalarMap_center G I p hp hR hA hspan iY g H

include hA hspan in
set_option backward.isDefEq.respectTransparency false in
/-- 同じ native なスカラーの四角形の全複体は、標準開被覆で完全。
BST13 Lemma 3.9・BS17 Lemma 4.6(i) に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem projectivePerfectCartesianScalarSquare_standard_acyclic :
    (projectivePerfectCartesianScalarSquare G I iY g H p hp hR
      (projectiveProjCechOpen (ι := ι) G)).totalComplex.Acyclic := by
  let m := projectivePerfectCartesianToScalarSquare G I p hp hR hA hspan iY g H
  apply (m.totalComplex_acyclic_iff_of_cones ?_ ?_ ?_ ?_).mp
    (projectivePerfectCartesianSquare_acyclic G I p hp hR hA hspan iY g H)
  · apply cechRefinementCone_acyclic_of_quasiIso
    intro q
    change QuasiIsoAt (𝟙 (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).C) q
    infer_instance
  · apply cechRefinementCone_acyclic_of_quasiIso
    intro q
    change QuasiIsoAt (𝟙 (projectivePerfectCartesianAugmentedSquare (ι := ι) G I p hp hR hA hspan iY g H).E) q
    infer_instance
  · exact Function.bijective_id
  · exact Function.bijective_id

end SerrePositivity.AlgebraicGeometry
