module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomDerivedCompositionPrismRecovery
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ArrowCalculus.RelativePrismEdgeClass
/-! # 明示係数 prism と指定対角辺の正本端点での相対比較

概要：明示 augmentation prism を、正本端点のまま指定係数対角変形へ両端固定で移す。
方針：既存の pinched 相対正規化を同じ区間比較で写し、指定変形の全 prism 表示を使う。
規約：元 Hom 入力・全時間・両端の全時間固定を保持する。
使われ方：六片から得る係数対角の辺の類を、指定係数対角辺へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarParameter R C D M X Y

def dgGluingHomDerivedCanonicalAugmentationIntervalPrism :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedAugmentationPrism R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _

lemma dgGluingHomDerivedCanonicalAugmentationNormalization_exists :
    ∃ H : SSet.Homotopy (dgGluingHomDerivedCanonicalAugmentationIntervalPrism R C D M X Y)
        ((β_ (Δ[1] : SSet.{max (u + 1) v w}) K).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h),
      (((boundary 1).ι ▷ K) ▷ (Δ[1] : SSet.{max (u + 1) v w})) ≫ H.h =
        fst ((boundary 1 : SSet.{max (u + 1) v w}) ⊗ K) Δ[1] ≫ ((boundary 1).ι ▷ K) ≫
          (β_ (Δ[1] : SSet.{max (u + 1) v w}) K).hom ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h := by
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedAugmentationNormalization_exists R C D M X Y
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.left)))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y.right)))
  let T := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H q
  have hG : uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) ≫ q =
      (β_ (Δ[1] : SSet.{max (u + 1) v w}) K).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionDiagonalHomotopy_canonical_prism R C D M X Y]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  let U := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget T rfl hG
  refine ⟨U, ?_⟩
  have hU : U.h = H.h ≫ q := rfl
  rw [hU]
  calc
    _ = fst ((boundary 1 : SSet.{max (u + 1) v w}) ⊗ K) Δ[1] ≫
        ((boundary 1).ι ▷ K) ≫
          (uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) ≫ q) := by
      have he := congrArg (fun f => f ≫ q) hH
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarParameter, Category.assoc] using he
    _ = _ := by rw [hG]

def dgGluingHomDerivedAugmentationDiagonalHomotopy :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyOfRelativePrism (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y)
    (Classical.choose (dgGluingHomDerivedCanonicalAugmentationNormalization_exists R C D M X Y))
    (Classical.choose_spec
      (dgGluingHomDerivedCanonicalAugmentationNormalization_exists R C D M X Y))

lemma dgGluingHomDerivedAugmentationDiagonalHomotopy_h :
    (dgGluingHomDerivedAugmentationDiagonalHomotopy R C D M X Y).h =
      (β_ K (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
        dgGluingHomDerivedCanonicalAugmentationIntervalPrism R C D M X Y := rfl

lemma dgGluingHomDerivedAugmentationDiagonalHomotopy_class :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (dgGluingHomDerivedAugmentationDiagonalHomotopy R C D M X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyOfRelativePrism_homMk_eq _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
