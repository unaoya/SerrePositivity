module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects

/-!
概要：写像空間の局所性から通常のホモトピー圏の Hom の全単射を回収する。
方針：一点の定値族の前合成を評価し、元の端点への移送と合成を保持する。
規約：高次の局所性からの帰結であり、逆向きの判定とは扱わない。
使われ方：HTT 5.5.4 の局所対象への置換間の射の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

private lemma localConstantVertex {A X : SSet.{u}} (a : A _⦋0⦌) (x : X _⦋0⦌) :
    (SSet.const x : A ⟶ X).app (Opposite.op ⦋0⦌) a = x := by
  simp [SSet.const]

private def localConstantHomEvaluate {A X : SSet.{u}} (a : A _⦋0⦌)
    {x y : X _⦋0⦌} (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X x y) :
    (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y :=
  eqToHom (congrArg HomotopyCategory.mk (localConstantVertex a x)).symm ≫
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α a ≫ eqToHom (congrArg HomotopyCategory.mk (localConstantVertex a y))

private lemma localConstantHomEvaluate_comp {A X : SSet.{u}} (a : A _⦋0⦌)
    {x y z : X _⦋0⦌} (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X x y) (β : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X y z) :
    localConstantHomEvaluate a (α ≫ β) =
      localConstantHomEvaluate a α ≫ localConstantHomEvaluate a β := by
  simp [localConstantHomEvaluate, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp, Category.assoc]

private lemma localConstantHomEvaluate_map {A X : SSet.{u}} (a : A _⦋0⦌) {x y : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    localConstantHomEvaluate a (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A f) = f := by
  unfold localConstantHomEvaluate
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap, Functor.map_comp, eqToHom_map]
  simp only [← Category.assoc, eqToHom_trans]
  simp only [Category.assoc, eqToHom_trans]
  let C := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A X)).toFunctor
  let E := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a)).toFunctor
  have hCE : C ⋙ E = 𝟭 (hoFunctor.obj X) := by
    change (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A X) ≫
      hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a)).toFunctor = _
    rw [← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorMap_evaluate, CategoryTheory.Functor.map_id]
    rfl
  have hm := CategoryTheory.Functor.congr_hom hCE f
  have hh := congrArg (fun g ↦
    eqToHom (CategoryTheory.Functor.congr_obj hCE (HomotopyCategory.mk x)).symm ≫ g ≫
    eqToHom (CategoryTheory.Functor.congr_obj hCE (HomotopyCategory.mk y))) hm
  dsimp only [C, E] at hh
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] at hh
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] at hh
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hh
  exact hh

/-- 写像空間の前合成が同値なら、元のホモトピー圏の Hom の前合成は全単射。 -/
lemma isLocalForHom_hom_bijective {X : SSet.{u}} [Quasicategory X]
    {x y z : X _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom f z) :
    Function.Bijective (fun g : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶
      HomotopyCategory.mk z ↦ f ≫ g) := by
  let A := (Δ[0] : SSet.{u})
  let a : A _⦋0⦌ := stdSimplex.obj₀Equiv.symm 0
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_constantHom_bijective f hf A
  constructor
  · intro g g' hg
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorHomMap_injective a y z
    apply h.1
    simp only [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp, hg]
  · intro g
    obtain ⟨α, hα⟩ := h.2 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A g)
    refine ⟨localConstantHomEvaluate a α, ?_⟩
    have he := congrArg (localConstantHomEvaluate a) hα
    simpa only [localConstantHomEvaluate_comp, localConstantHomEvaluate_map] using he

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
