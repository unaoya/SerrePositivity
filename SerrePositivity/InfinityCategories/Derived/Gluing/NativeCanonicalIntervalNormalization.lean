module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeCanonicalIntervalFace
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedAugmentationIntervalNormalization
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativePrismHomotopyPrecomp

/-! # 実正規化 prism と主係数 path の相対比較

概要：実加群からの正規化 prism を、主係数 path の区間族と両端固定で比較する。
方針：canonical 係数の厳密等式を区間 Hom へ送り、既存の相対正規化を制限する。
規約：同じ元 Hom 入力と全時間を保ち、端点を固定する等式も保持する。
使われ方：実後 cube の区間面と入力固定変形の二次元相対比較を接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)


/-- 概要：実加群の正規化 prism を導来加群の区間 Hom へ送る。
方針：宇宙同型の順射と実導来関手の Hom 作用を後合成する。
規約：元の pinched Hom を入力とする。使われ方：cube から得る実区間面の比較。 -/
def dgGluingNativeDerivedNormalizedIntervalPrism :=
  dgGluingNativeModuleNormalizedPrism R C D M X Y ≫
    (uliftPinchedHomIso.{max (u + 1) v, max (u + 1) v w}
      (C := dgNerve R (RightModule R C))
      (Simplex.vertex (representable R X.left)) (Simplex.vertex (M.rightAt Y.right))).hom ≫
    pinchedHomMap (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
      (ULift.up (Simplex.vertex (representable R X.left)))
      (ULift.up (Simplex.vertex (M.rightAt Y.right))) ≫
    pinchedHomToIntervalMappingSpace _ _

lemma dgGluingNativeDerivedNormalizedIntervalPrism_factor :
    dgGluingNativeDerivedNormalizedIntervalPrism R C D M X Y =
      (Δ[1] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
        dgGluingHomDerivedAugmentationIntervalPrism R C D M X Y := by
  have he := congrArg (fun f => f ≫ pinchedHomToIntervalMappingSpace _ _)
    (dgGluingCanonicalCoefficientMappingComparison_universe_action R C D M X.left Y.right)
  simp only [Category.assoc] at he
  rw [dgGluingNativeDerivedNormalizedIntervalPrism, ← he]
  rw [← Category.assoc (dgGluingNativeModuleNormalizedPrism R C D M X Y),
    dgGluingNativeNormalizedPrism_canonical_coefficient]
  simp only [dgGluingHomDerivedAugmentationIntervalPrism,
    dgGluingHomDerivedAugmentationPrism, Category.assoc]

lemma dgGluingNativeDerivedNormalizedIntervalPrism_normalization_exists :
    ∃ H : SSet.Homotopy (dgGluingNativeDerivedNormalizedIntervalPrism R C D M X Y)
        ((Δ[1] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
          dgGluingHomDerivedCoefficientIntervalPrism R C D M X Y),
      (((boundary 1).ι ▷ ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y))) ▷ (Δ[1] : SSet.{max (u + 1) v w})) ≫ H.h =
        fst ((boundary 1 : SSet.{max (u + 1) v w}) ⊗ ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y))) Δ[1] ≫
          ((boundary 1).ι ▷ ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y))) ≫ (Δ[1] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
            dgGluingHomDerivedCoefficientIntervalPrism R C D M X Y := by
  rw [dgGluingNativeDerivedNormalizedIntervalPrism_factor]
  obtain ⟨H, hH⟩ := dgGluingHomDerivedAugmentationIntervalNormalization_exists R C D M X Y
  refine ⟨functorHomotopyPrecomp H (Δ[1] ◁ dgGluingNativeHomModelMap R C D M X Y), ?_⟩
  exact dgGluingRelativePrismHomotopy_precomp_boundary H
    (dgGluingNativeHomModelMap R C D M X Y) hH

end SerrePositivity.InfinityCategories
