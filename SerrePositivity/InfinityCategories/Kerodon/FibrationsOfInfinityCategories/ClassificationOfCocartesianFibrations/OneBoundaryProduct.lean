module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.PullbackTerminalProductIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.HornBoundaryHomPullbacks
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ZeroBoundaryComparison

/-!
概要：一次元標準境界上の元の native Hom と分類先 Hom を、同じ両端の直積へ分解する。
方針：空の共有境界上の終対象性と、同じホーン・面の厳密な pullback を使う。
規約：両射影は実際の二端点への直接制限を保持する。
使われ方：両端の零次元比較から一次元境界の比較を構成する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {B : SSet.{u}} (i : Fin 2) (σ : (Δ[1] : SSet.{u}) ⟶ B)

section Source
variable {E F : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]

/-- 元の一次元境界の native core と、同じ両端の native core の直積の同型。 -/
def cocartesianOneBoundaryNativeProductIso :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackTerminalProductIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHornBoundary_native_isPullback 0 i σ p q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLift_isTerminal_of_isInitial p q
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.shared 0 i σ) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.zeroSimplexBoundary_isInitial)

/-- 同じ native 積分解の第一射影は、元の面側の端点制限。 -/
lemma cocartesianOneBoundaryNativeProductIso_hom_fst :
    (cocartesianOneBoundaryNativeProductIso i σ p q).hom ≫ fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.faceInclusion 0 i σ) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackTerminalProductIso_hom_fst _ _

/-- 同じ native 積分解の第二射影は、元のホーン側の端点制限。 -/
lemma cocartesianOneBoundaryNativeProductIso_hom_snd :
    (cocartesianOneBoundaryNativeProductIso i σ p q).hom ≫ snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeLiftPre p q (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.hornInclusion 0 i σ) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackTerminalProductIso_hom_snd _ _
end Source

section Target
variable {X : SSet.{u + 1}} (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X)

/-- 同じ一次元境界の分類先 Hom も、同じ両端の Hom の直積と同型。 -/
def cocartesianOneBoundaryIntervalProductIso :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackTerminalProductIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHornBoundary_interval_isPullback 0 i σ P Q)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.intervalDiagramHom_isTerminal_of_isInitial _ _
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.uliftSSet_isInitial_of_isInitial _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.zeroSimplexBoundary_isInitial))

/-- 同じ target 積分解の第一射影も、元の面側の端点制限。 -/
lemma cocartesianOneBoundaryIntervalProductIso_hom_fst :
    (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom ≫ fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre P Q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.faceInclusion 0 i σ)) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackTerminalProductIso_hom_fst _ _

/-- 同じ target 積分解の第二射影も、元のホーン側の端点制限。 -/
lemma cocartesianOneBoundaryIntervalProductIso_hom_snd :
    (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom ≫ snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalDiagramOverPre P Q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.hornInclusion 0 i σ)) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackTerminalProductIso_hom_snd _ _
end Target

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
