module

public import SerrePositivity.EInfinity.BarrattEccles.CAlgDiscreteDerivedComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiscreteCharacterization

/-!
# 同じ U による離散入力の像の離散性

概要：実離散 CAlg_R 入力の U 像は零次以外のホモロジーが消える。
方針：既存埋め込みとの全関手比較の同じ成分で消滅を移す。
規約：既存 derivedInfinityDisc と同じ全整数次数の条件。
使われ方：E2b の離散入力。離散対象の本質像の逆包含は後続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma discreteDerivedEmbedding_vertex (B : Under (CommRingCat.of A)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteEmbedding A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleHeartVertex A ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A).obj B) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A)).injective
  rfl

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma discreteDerivedEmbedding_disc (B : Under (CommRingCat.of A)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityDisc ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteEmbedding A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B)) := by
  rw [discreteDerivedEmbedding_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleHeartVertex_disc _

def cAlgUnderlyingDisc (x : (CAlg_R A) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityDisc ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌) x)

lemma discreteCAlgUnderEmbedding_underlyingDisc (B : Under (CommRingCat.of A)) :
    cAlgUnderlyingDisc A
      ((discreteCAlgUnderEmbedding A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B)) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app (discreteCAlgUnderEmbedding_forgetIso A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B)
  have e' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory
    ((truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A))).mapIso e
  intro i hi
  exact (discreteDerivedEmbedding_disc A B i hi).of_iso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyFunctor A i).mapIso e')

end SerrePositivity.EInfinity.BarrattEccles
