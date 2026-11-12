module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationReflection
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseHorns
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallSimplicialSet

/-! # 同じホーンを保つ quasicategory 性の宇宙降下と小さい模型 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.Fibration

/-- 元の全内ホーンを持ち上げて充填し、同じ各面とともに宇宙を降ろす。 -/
theorem quasicategory_of_ulift (X : SSet.{u})
    [Quasicategory ((SSet.uliftFunctor.{v, u}).obj X)] : Quasicategory X := by
  constructor
  intro n i σ h₀ hₙ
  let a := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, v} (n + 2) i).inv ≫ (SSet.uliftFunctor.{v, u}).map σ
  obtain ⟨φ, hφ⟩ := Quasicategory.hornFilling h₀ hₙ a
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown φ, ?_⟩
  apply horn.hom_ext'
  intro j hj
  rw [horn.ι_ι_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftSimplexHomDown_face]
  have he : stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftSimplexHomUp.{u, v} (horn.ι i j hj ≫ σ) := by
    calc
      _ = horn.ι i j hj ≫ (horn (n + 2) i).ι ≫ φ := (horn.ι_ι_assoc i j hj φ).symm
      _ = horn.ι i j hj ≫ a := congrArg (fun m => horn.ι i j hj ≫ m) hφ.symm
      _ = _ := by
        apply yonedaEquiv.injective
        simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftSimplexHomUp, Equiv.apply_symm_apply]
        rfl
  rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftSimplexHomDown_up]

/-- 各次数で小さい quasicategory の縮小は、全単体の同型と同じホーン充填を保つ。 -/
instance smallSimplicialSet_quasicategory (X : SSet.{max u v})
    [∀ n, Small.{u} (X.obj n)] [Quasicategory X] : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet X) := by
  have : Quasicategory ((SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet X)) :=
    quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso X).hom
  exact quasicategory_of_ulift _

end SerrePositivity.KST.Fibration
