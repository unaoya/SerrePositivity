module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.OppositeKanUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftStrictTransportReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence

/-!
概要：通常の nerve 上の left fibration を coherent な空間値図式の unstraightening と比較する。
方針：値を反転した strict transport を coherent 図式とし、weighted nerve と共通の比較空間を経由する。
規約：底と全空間を u+1 に持ち上げる。一般の coherent 図式の分類の一意性は別に証明する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、left fibration の coherent な表現の存在方向。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：left fibration の strict transport の値を反転して coherent な 𝒮 値図式にする。
方針：strict transport の Kan 値関手に反転関手を合成し、coherent nerve の表示を使う。
規約：値の反転は weighted nerve と coslice の比較の規約を揃えるために明示する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、通常の底上の left fibration の coherent な表現。 -/
noncomputable def leftCoherentTransport
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor)

/-- 概要：strict transport の weighted nerve から coherent な表現の unstraightening への比較射。
方針：元の係数による反転した Kan 図式の比較を strict transport に適用する。
規約：比較の始域の係数に追加の反転はない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元への実際の比較。 -/
noncomputable def leftCoherentTransportComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportWeightedNerve p) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (leftCoherentTransport p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.oppositeKanUnstraighteningComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p)

/-- 概要：coherent transport の比較射は元の底の持ち上げを厳密に保つ。
方針：反転した Kan 図式への比較の射影の式を使う。
規約：始域の射影は strict transport の weighted nerve の標準射影。
使われ方：Kerodon §5.6.2（Tag 026H）、coherent な復元の底上の図式。 -/
lemma leftCoherentTransportComparison_projection
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    leftCoherentTransportComparison p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (leftCoherentTransport p) =
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportWeightedProjection p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.oppositeKanUnstraighteningComparison_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p)

/-- 概要：coherent transport の weighted nerve からの比較射は前合成同値。
方針：一般の反転した Kan 図式の比較の同値性を適用する。
規約：底上の実際の射の性質として示す。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な表現の復元比較。 -/
lemma leftCoherentTransportComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (leftCoherentTransportComparison p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.oppositeKanUnstraighteningComparison_isPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p)

/-- 概要：元の left fibration と coherent transport の unstraightening は底上の同値の span で結ばれる。
方針：scaffold の共通の比較を宇宙持ち上げし、weighted nerve からの coherent な比較を合成する。
規約：共通の始域は inner fibration の全空間であり、left fibration 性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な表現の存在方向の全空間比較。 -/
lemma exists_leftCoherentTransport_reconstruction_span
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    ∃ (Z : SSet.{u + 1})
      (t : Z ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve C))
      (a : Z ⟶ (SSet.uliftFunctor.{u + 1, u}).obj E)
      (b : Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (leftCoherentTransport p)),
      InnerFibration t ∧ a ≫ (SSet.uliftFunctor.{u + 1, u}).map p = t ∧
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (leftCoherentTransport p) = t ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence a ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence b := by
  obtain ⟨Z, t, a, b, ht, ha, hb, ea, eb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.exists_leftStrictTransport_reconstruction_span p
  have : InnerFibration t := ht
  have : Quasicategory Z := quasicategory_of_innerFibration t
  have : Quasicategory E := quasicategory_of_innerFibration p
  let U := SSet.uliftFunctor.{u + 1, u}
  refine ⟨U.obj Z, U.map t, U.map a, U.map b ≫ leftCoherentTransportComparison p,
    inferInstance, ?_, ?_, ea.isQCatEquivalence.ulift.isPrecompositionEquivalence,
    eb.isQCatEquivalence.ulift.isPrecompositionEquivalence.comp
      (leftCoherentTransportComparison_isPrecompositionEquivalence p)⟩
  · rw [← U.map_comp, ha]
  · rw [Category.assoc, leftCoherentTransportComparison_projection, ← U.map_comp, hb]

/-- 概要：通常の nerve 上の left fibration の持ち上げた全空間は coherent な表現の unstraightening と同値。
方針：底上の span の二つの前合成同値を quasicategory の同値にし、一方を逆に合成する。
規約：底を厳密に保つ比較データは span に保持し、結論では全空間の同値の非空性を述べる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、通常の圏上の coherent な表現の存在方向。 -/
lemma nonempty_leftCoherentTransportEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (leftCoherentTransport p))) := by
  obtain ⟨Z, t, a, b, ht, _, _, ea, eb⟩ := exists_leftCoherentTransport_reconstruction_span p
  have : InnerFibration t := ht
  have : Quasicategory Z := quasicategory_of_innerFibration t
  exact ⟨ea.isQCatEquivalence.choose.symm.trans eb.isQCatEquivalence.choose⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
