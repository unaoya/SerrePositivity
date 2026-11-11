module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredLeftFibrationDetection

/-!
概要：filtered な底の全空間の有限な相対図式を同じ fiber の Kan 置換で検出する。
方針：境界を含む有限部分複体の共通段へ因子分解し、その全体を一つの fiber へ輸送する。
規約：輸送後の境界の等式と、元の境界・全体への実際のホモトピーを保持する。
使われ方：一般 coherent な filtered 図式での有限射と境界条件の同時検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

/-- 概要：全空間模型への有限な射と元の境界を、一つの fiber へ同時に移せる。
方針：連続置換の相対因子分解と有限部分複体の fiber 輸送を合成する。
規約：境界は輸送後に厳密に一致し、元の両指定射へのホモトピーを返す。 -/
lemma continuousKanLeftFibration_finite_relative_detection {A K E B : SSet.{u}}
    [A.Finite] [K.Finite] [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (i : A ⟶ K) (a : A ⟶ E)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E = i ≫ f) :
    ∃ b : B _⦋0⦌, ∃ t : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b,
      ∃ g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b),
        i ≫ g = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) ∧
        Nonempty (SSet.Homotopy a (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)) ∧
        Nonempty (SSet.Homotopy f (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b))) := by
  obtain ⟨j, a₀, ha₀⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finiteSubcomplex_factorization a
  have hh : (a₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app j.val) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map j.val.ι = i ≫ f := by
    rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality j.val.ι,
      CategoryTheory.Functor.id_map, ← Category.assoc, ha₀]
    exact h
  obtain ⟨k, v, r, hi, hr⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finiteSubcomplex_relative_factorization_after_preserving_functor
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement E i j (a₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app j.val) f hh
  let v' := Subcomplex.homOfLE (leOfHom v)
  let a' := a₀ ≫ v'
  have ha' : a' ≫ k.val.ι = a := by
    dsimp only [a', v']
    rw [Category.assoc, Subcomplex.homOfLE_ι, ha₀]
  obtain ⟨b, s, ⟨H⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.leftFibration_finite_fiber_detection p k.val.ι
  refine ⟨b, a' ≫ s, r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map s, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hi, Category.assoc, Category.assoc,
      ← CategoryTheory.Functor.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality]
    simp only [CategoryTheory.Functor.id_map, a', v', Category.assoc]
  · have H' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H a'
    simpa only [← Category.assoc, ha'] using Nonempty.intro H'
  · obtain ⟨H'⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_map_homotopy H
    have H'' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H' r
    simpa only [CategoryTheory.Functor.map_comp, ← Category.assoc, hr] using Nonempty.intro H''

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
