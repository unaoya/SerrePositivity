module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexCellMono
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexLocalNaturality
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLifting

/-!
概要：同じ二辺と共有頂点の標的 cospan の両脚は、指定された可逆 path を持ち上げる。
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

/-- 同じ単射な底上の射に沿う区間 Hom 制限は、可逆 path の相対持ち上げを持つ。 -/
lemma kanEquivalenceLifting_intervalDiagramOverPre {B X : SSet.{u}} [Quasicategory X]
    (F G : B ⟶ X) {a b : Over B} (i : a ⟶ b) [Mono i.left] :
    F1B.KanEquivalenceLifting (intervalDiagramOverPre F G i) :=
  kanEquivalenceLifting_intervalMappingPostOfEq ((pre i.left).app X)
    (F1B.kanEquivalenceLifting_pre i.left) _ _ _ _

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の標的 cospan の最初の脚は、指定された可逆 path を持ち上げる。 -/
lemma cocartesianTwoSimplexLocalTarget_first_kanEquivalenceLifting :
    F1B.KanEquivalenceLifting
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl) := by
  have : Mono (uliftOverMorphism.{u, u + 1}
      (cocartesianTwoSimplexSharedToFirst k)).left := by
    change Mono ((SSet.uliftFunctor.{u + 1, u}).map
      (cocartesianTwoSimplexSharedToFirst k).left)
    exact SimplicialModel.UniverseLift.mono_map _
  intro T U j hj he
  exact kanEquivalenceLifting_intervalDiagramOverPre
    (B := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (X := CatInfinity.{u})
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (uliftOverMorphism (cocartesianTwoSimplexSharedToFirst k)) j hj he

/-- 元の標的 cospan の次の脚も、同じ共有頂点で可逆 path を持ち上げる。 -/
lemma cocartesianTwoSimplexLocalTarget_second_kanEquivalenceLifting :
    F1B.KanEquivalenceLifting
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr) := by
  have : Mono (uliftOverMorphism.{u, u + 1}
      (cocartesianTwoSimplexSharedToSecond k)).left := by
    change Mono ((SSet.uliftFunctor.{u + 1, u}).map
      (cocartesianTwoSimplexSharedToSecond k).left)
    exact SimplicialModel.UniverseLift.mono_map _
  intro T U j hj he
  exact kanEquivalenceLifting_intervalDiagramOverPre
    (B := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (X := CatInfinity.{u})
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (uliftOverMorphism (cocartesianTwoSimplexSharedToSecond k)) j hj he

end SerrePositivity.InfinityCategories
