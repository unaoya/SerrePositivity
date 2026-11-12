module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulIsoRecovery
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ReconstructionHomRecovery

/-!
概要：全空間へ回収した復元同型は、元の scaffold の標準 Hom の族の同型を保つ。
方針：充満忠実な後合成の回収の往復則を実際の復元同型へ適用する。
規約：同じ始域・標的の同型の存在だけで代用しない。
使われ方：weighted nerve と反転 unstraightening の共同比較の照合。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance {B : SSet.{u}} :
    ∀ X Y : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)ᵒᵖ, KanComplex (SimplicialCategory.sHom X Y) :=
  fun X Y ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- 回収した全空間の復元同型は、元の scaffold の同じ全標的の Hom の族の同型へ戻る。 -/
lemma leftStrictTransportReconstructionOppositeIso_testFamily
    (C : Type u) [Category.{u} C] :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.leftStrictTransportReconstructionOppositeIso C).postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationHomTestFamily (nerve C)) =
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.leftStrictTransportReconstructionHomFamilyIso C := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.leftStrictTransportReconstructionOppositeIso
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftFibrationHomTestFamily_isFullyFaithful (nerve C)).preimageFunctorIso_postcomp _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
