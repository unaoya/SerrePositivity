module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportEnrichedFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningEvaluation

/-!
概要：strict transport の像の対象ごとの豊穣評価と、既存の coherent な straightening の評価との整合性。
方針：strict な変換の成分を豊穣 Hom の作用とし、相対 Hom の後合成との厳密な一致を使う。
規約：底の対象 c は固定するが、fibration の coherent パラメーターは全次数で動かす。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、中間の coherent nerve と空間値の関手 ∞ 圏への比較の接続。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：strict transport の像の図式を指定した底の対象で評価する豊穣関手。
方針：strict な変換の対象成分を Hom の作用とし、成分での単位・合成の計算則を使う。
規約：標的は coherent nerve を取る前の KanObject の単体的圏。
使われ方：Kerodon §5.3.1（Tag 035D）、Corollary 5.6.0.6（Tag 028T）、coherent な評価を作る豊穣的な入力。 -/
def strictTransportDiagramEvaluationEnriched {C : Type u} [Category.{u} C] (c : C) :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagramObject C) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj F := F.val.obj c
  map F G := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) c
  map_id F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity_component (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) c
  map_comp F G H := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition_component
    (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (H.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) c

/-- 概要：strict transport の像の coherent nerve から 𝒮 への対象ごとの評価関手。
方針：対象ごとの豊穣評価に coherent nerve を適用する。
規約：元の図式の対象と高次の変換の族を同じ評価で扱う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、関手 ∞ 圏への比較を値で検証する評価射。 -/
noncomputable def strictTransportDiagramInfinityEvaluation {C : Type u} [Category.{u} C] (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportDiagramInfinity C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (strictTransportDiagramEvaluationEnriched c)

/-- 概要：strict transport を取って対象 c で評価する豊穣関手は undercategory 上の相対 Hom の評価と一致する。
方針：対象は定義で比較し、Hom の作用は strict transport の成分の計算則を使う。
規約：豊穣関手そのものの厳密な等式。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、coherent な評価の比較の全次数の自然性の基礎。 -/
lemma leftStrictTransportEnriched_evaluate {C : Type u} [Category.{u} C] (c : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportEnriched (C := C)).comp SSet (strictTransportDiagramEvaluationEnriched c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (Over.mk (nerveMap (Under.forget c))) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro p q
  simp only [eqToHom_refl, Category.comp_id]

/-- 概要：strict transport の像への coherent な比較を c で評価すると元の相対 Hom の coherent 評価を得る。
方針：coherent nerve が豊穣合成を保つことと、豊穣評価の厳密な一致を使う。
規約：fibration のすべての coherent な高次パラメーターを含む射の等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、既存の straightening の値での作用との接続。 -/
lemma leftStrictTransportInfinityMap_evaluate {C : Type u} [Category.{u} C] (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportInfinityMap C ≫ strictTransportDiagramInfinityEvaluation c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportCoherentEvaluation c := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportEnriched (C := C)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (strictTransportDiagramEvaluationEnriched c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (Over.mk (nerveMap (Under.forget c))))
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, leftStrictTransportEnriched_evaluate]

/-- 概要：strict transport の像への比較と既存の関手 ∞ 圏への straightening は、全対象で同じ coherent 評価を持つ。
方針：二つの評価を undercategory 上の相対 Hom の coherent 評価へ同定する。
規約：この値ごとの一致だけから関手 ∞ 圏への同値性は推論しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、中間の単体的圏と既存の分類候補の写像空間の接続。 -/
lemma leftStrictTransportInfinityMap_evaluate_straightening
    {C : Type u} [Category.{u} C] (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportInfinityMap C ≫ strictTransportDiagramInfinityEvaluation c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  rw [leftStrictTransportInfinityMap_evaluate, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCoherentMap_evaluate]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
