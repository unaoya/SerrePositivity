module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.HornBoundaryFibers
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CellAttachmentFibrations

/-!
概要：標準境界のホーンへの制限と欠けた面の境界制限は、両側で Kan fibration。
方針：同じ四つの標準包含の単射性を、元の native core と区間 Hom の制限へ移す。
規約：実際の指定ホーン値の延長空間も Kan と証明する。
使われ方：境界比較の帰納の fiber 判定。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {B : SSet.{u}} (n : ℕ) (i : Fin (n + 2)) (σ : (Δ[n + 1] : SSet.{u}) ⟶ B)

section Source
variable {E F : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]

/-- 同じ標準境界からホーンへの native core 制限は Kan fibration。 -/
lemma cocartesianHornBoundary_nativeRestriction_fibration :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.hornInclusion n i σ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre_fibration p q (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.hornInclusion n i σ)

/-- 同じ欠けた標準面から共有境界への native core 制限は Kan fibration。 -/
lemma cocartesianHornBoundary_nativeFaceRestriction_fibration :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.toFace n i σ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre_fibration p q (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.toFace n i σ)

/-- 元のホーン上の指定 native Hom を境界へ延長する実際の空間は Kan。 -/
lemma cocartesianHornBoundary_nativeExtension_kanComplex
    (r : ((SSet.uliftFunctor.{u + 1, u}).obj
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeCoreFunctor p q).obj
        (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.horn n i σ)))) _⦋0⦌) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.hornInclusion n i σ)) r) := by
  letI := cocartesianHornBoundary_nativeRestriction_fibration n i σ p q
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration _ _
end Source

section Target
variable {X : SSet.{u + 1}} [Quasicategory X]
  (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X)

/-- 分類先の同じ標準境界からホーンへの制限も Kan fibration。 -/
lemma cocartesianHornBoundary_intervalRestriction_fibration :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre P Q
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.hornInclusion n i σ))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianCellAttachment_intervalRestriction_fibration
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.toFace n i σ) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.toHorn n i σ)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.faceInclusion n i σ) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.hornInclusion n i σ)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.isPushout n i σ) P Q

/-- 分類先の同じ欠けた面から共有境界への制限も Kan fibration。 -/
lemma cocartesianHornBoundary_intervalFaceRestriction_fibration :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre P Q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.toFace n i σ))) := by
  letI : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.toFace n i σ)).left :=
    SimplicialModel.UniverseLift.mono_map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.toFace n i σ).left
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre_fibration P Q _

/-- 分類先のホーン上の指定 Hom を境界へ延長する実際の空間も Kan。 -/
lemma cocartesianHornBoundary_intervalExtension_kanComplex
    (r : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverFunctor P Q).obj (Opposite.op
      (Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.horn n i σ).hom)))) _⦋0⦌) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre P Q
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.hornInclusion n i σ))) r) := by
  letI := cocartesianHornBoundary_intervalRestriction_fibration n i σ P Q
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration _ _
end Target

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
