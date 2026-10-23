module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldCellMono
public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldLocalNaturality
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexLocalPathLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLifting

/-!
概要：同じ最初の辺と尾部と共有頂点の標的 cospan の両脚は、指定された可逆 path を持ち上げる。
方針：同じ単射な包含への前合成と区間 Hom の後合成の持ち上げを合成する。
規約：追加の持ち上げ仮定を置かず、元の制限写像について証明する。
使われ方：元の局所 cospan 比較の path を保った厳密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の標的 cospan の最初の脚は、指定された可逆 path を持ち上げる。 -/
lemma cocartesianScaffoldLocalTarget_first_kanEquivalenceLifting :
    F1B.KanEquivalenceLifting
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl) := by
  have : Mono (uliftOverMorphism.{u, u + 1}
      (cocartesianScaffoldSharedToFirst n k)).left := by
    change Mono ((SSet.uliftFunctor.{u + 1, u}).map
      (cocartesianScaffoldSharedToFirst n k).left)
    exact SimplicialModel.UniverseLift.mono_map _
  intro T U j hj he
  exact kanEquivalenceLifting_intervalDiagramOverPre
    (B := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (X := CatInfinity.{u})
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (uliftOverMorphism (cocartesianScaffoldSharedToFirst n k)) j hj he

/-- 元の標的 cospan の次の脚も、同じ共有頂点で可逆 path を持ち上げる。 -/
lemma cocartesianScaffoldLocalTarget_second_kanEquivalenceLifting :
    F1B.KanEquivalenceLifting
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr) := by
  have : Mono (uliftOverMorphism.{u, u + 1}
      (cocartesianScaffoldSharedToTail n k)).left := by
    change Mono ((SSet.uliftFunctor.{u + 1, u}).map
      (cocartesianScaffoldSharedToTail n k).left)
    exact SimplicialModel.UniverseLift.mono_map _
  intro T U j hj he
  exact kanEquivalenceLifting_intervalDiagramOverPre
    (B := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (X := CatInfinity.{u})
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (uliftOverMorphism (cocartesianScaffoldSharedToTail n k)) j hj he

end SerrePositivity.InfinityCategories
