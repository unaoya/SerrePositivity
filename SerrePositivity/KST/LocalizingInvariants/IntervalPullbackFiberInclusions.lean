module

public import SerrePositivity.KST.LocalizingInvariants.IntervalFiberGroupoidCompletion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.VertexFiberNervePullback

/-!
概要：区間の引き戻し全体への元の両端 fiber の包含と、亜群化後の同値性。
方針：底変換の実 fiber 同型の逆と元の fiber 包含を合成する。
規約：元の全空間と区間への両射影を保持。使われ方：元の輸送 prism の底変換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def intervalPullbackFiberInclusion {E B : SSet.{u}} (p : E ⟶ B)
    (b : (Δ[1] : SSet.{u}) ⟶ B) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i)) ⟶ pullback p b :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p b (stdSimplex.obj₀Equiv.symm i)).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd p b) (stdSimplex.obj₀Equiv.symm i)

lemma intervalPullbackFiberInclusion_fst {E B : SSet.{u}} (p : E ⟶ B)
    (b : (Δ[1] : SSet.{u}) ⟶ B) (i : Fin 2) :
    intervalPullbackFiberInclusion p b i ≫ pullback.fst p b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i)) := by
  dsimp only [intervalPullbackFiberInclusion]
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι, Iso.inv_hom_id_assoc]

lemma intervalPullbackFiberInclusion_snd {E B : SSet.{u}} (p : E ⟶ B)
    (b : (Δ[1] : SSet.{u}) ⟶ B) (i : Fin 2) :
    intervalPullbackFiberInclusion p b i ≫ pullback.snd p b =
      SSet.const (stdSimplex.obj₀Equiv.symm i) := by
  dsimp only [intervalPullbackFiberInclusion]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]

lemma intervalPullbackFiberInclusion_zero_groupoidCompletion_isEquivalence
    {E B : SSet.{u}} (p : E ⟶ B) (b : (Δ[1] : SSet.{u}) ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (pullback.snd p b)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf (intervalPullbackFiberInclusion p b 0)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p b (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).symm
  have h := e.isQCatEquivalence.comp
    (initialFiberGroupoidCompletionEquivalence 1 (pullback.snd p b)).isQCatEquivalence
  exact h.ofFunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_compIso _ _)

lemma intervalPullbackFiberInclusion_one_groupoidCompletion_isEquivalence
    {E B : SSet.{u}} (p : E ⟶ B) (b : (Δ[1] : SSet.{u}) ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (pullback.snd p b)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf (intervalPullbackFiberInclusion p b 1)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p b (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).symm
  have h := e.isQCatEquivalence.comp
    (finalFiberGroupoidCompletionEquivalence 1 (pullback.snd p b)).isQCatEquivalence
  exact h.ofFunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_compIso _ _)

end SerrePositivity.KST.LocalizingInvariants
