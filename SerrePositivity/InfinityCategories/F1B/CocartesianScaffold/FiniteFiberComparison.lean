module

public import SerrePositivity.InfinityCategories.F1B.CocartesianScaffold.Definition

public import SerrePositivity.InfinityCategories.F1.Scaffold.FiniteFiberGeometry

public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldFiniteTotalFibers
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldFiniteCylinderEndpoints
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-!
概要：有限鎖上の scaffold から区間の両端 fiber への比較。
方針：零頂点の fiber 比較と尾部の底変換を、区間の fiber との標準同型へ合成する。
規約：比較先の射影は元の射影と有限鎖から区間への射の合成。
使われ方：Kerodon Theorem 5.3.5.7、Theorem 5.2.4.1 の両端条件の検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_quasicategory_of_innerFibration

/-- 概要：cocartesian scaffold の零端の比較は前合成の同値条件を満たす。
方針：元の零頂点の比較の同値性と零 fiber 同型の前合成の同値性を合成する。
規約：区間の射影全体の fibration 性はここでは要求しない。
使われ方：Kerodon Theorem 5.3.5.7、Theorem 5.2.4.1 の零端条件。 -/
lemma CocartesianScaffold.finiteZeroFiber_isPrecompositionEquivalence
    (n : ℕ) {E : SSet.{u}} {p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))} [CocartesianFibration p]
    {F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}} [∀ c, Quasicategory (F.obj c)]
    {l : simplicialReplacement F ⟶ E} (hs : SerrePositivity.InfinityCategories.CocartesianScaffold p F l)
    (h : l ≫ p = simplicialReplacementProjection F) :
    IsPrecompositionEquivalence (SerrePositivity.InfinityCategories.scaffoldFiniteZeroFiberComparison n p F l h) := by
  have hf := hs.fiber
  exact (hf (ULift.up 0)).isPrecompositionEquivalence.comp
    (isPrecompositionEquivalence_of_iso (scaffoldFiniteTotalZeroFiberIso n p))

/-- 概要：終端の前合成の同値条件は尾部への底変換の比較の同値条件と同値。
方針：一 fiber 同型の前合成の同値性と二対三則を使う。
規約：始域の replacement の quasicategory 性を要求しない。
使われ方：Kerodon Theorem 5.3.5.7、尾部の帰納仮定を終端条件へ移す。 -/
lemma cocartesianScaffoldFiniteOneFiberComparison_isPrecompositionEquivalence_iff
    (n : ℕ) {E : SSet.{u}} (p : E ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    IsPrecompositionEquivalence (SerrePositivity.InfinityCategories.scaffoldFiniteOneFiberComparison n p F l h) ↔
      IsPrecompositionEquivalence (SerrePositivity.InfinityCategories.leftScaffoldBaseChange p F l h (scaffoldFiniteTail n)) := by
  have he := isPrecompositionEquivalence_of_iso (scaffoldFiniteTotalOneFiberIso n p)
  exact ⟨fun ht ↦ he.cancel_right ht, fun ht ↦ ht.comp he⟩

end SerrePositivity.InfinityCategories
