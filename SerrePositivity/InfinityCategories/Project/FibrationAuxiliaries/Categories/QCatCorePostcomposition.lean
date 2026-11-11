module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QCatCoherentPostcomposition

/-!
概要：元の core Hom の固定第二射による合成を、同じ内部 Hom の後合成と同定する。
方針：検証済みの宇宙持ち上げた等式を各単体で戻す。
規約：通常の射と元の core の全単体を保持する。
使われ方：第二三角形の始域から終域への Hom の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の core Hom と固定第二射の豊穣合成は、元の内部 Hom の後合成そのもの。 -/
lemma qCatCorePostcomposition_comp (A B Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (f : B ⟶ Z) :
    lift (𝟙 (SimplicialCategory.sHom A B))
        (SSet.const (SimplicialCategory.homEquiv' B Z f)) ≫ eComp SSet A B Z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom A.obj).map (show B.obj ⟶ Z.obj from f)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact congrArg (fun m ↦ (m.app n (ULift.up s)).down)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatCoherentCompositionFixedParameter_comp A B Z f)

/-- 零単体の定値な高次単体の Yoneda 族は、同じ零単体への定値射。 -/
lemma yonedaEquiv_symm_pinchedConstant {X : SSet.{u}} (x : X _⦋0⦌) (n : ℕ) :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n) = (SSet.const x : Δ[n] ⟶ X) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
