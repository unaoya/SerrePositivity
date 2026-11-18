module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationSpanStrictification
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldCoherentComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftCoherentTransportReconstruction

/-!
概要：元の left fibration から coherent transport の unstraightening への直接の底上の同値。
方針：復元 span の共通の定義域を相対関手空間の同値で消去し、一つの射を選ぶ。
規約：射の選択は非計算的。底上の可換性は厳密な等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、通常の底上の coherent な表現の存在方向。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：持ち上げた元の全空間から coherent transport の unstraightening への底上の同値射が存在する。
方針：復元 span に left fibration を標的とする比較の厳密化を適用する。
規約：単なる全空間の同値ではなく、底を保つ実際の射を結論とする。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な表現の存在方向の比較射。 -/
lemma exists_leftCoherentTransport_directComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    ∃ f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p),
      f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p) =
        (SSet.uliftFunctor.{u + 1, u}).map p ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f := by
  obtain ⟨Z, t, a, b, _, ha, hb, ea, eb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_leftCoherentTransport_reconstruction_span p
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_leftFibration_comparison_of_span
    ((SSet.uliftFunctor.{u + 1, u}).map p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p)) t a b ha hb ea eb

/-- 概要：coherent transport の unstraightening への直接の底上の比較射を選ぶ。
方針：相対写像空間から得た比較の存在を使う。
規約：定義域は元の全空間の u+1 への持ち上げ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、復元の比較射を使う側の API。 -/
noncomputable def leftCoherentTransportDirectComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p) :=
  scaffoldCoherentComparison p

/-- 概要：直接の coherent transport 比較は元の底の持ち上げを厳密に保つ。
方針：選択した比較の存在証明の底上の条件を取り出す。
規約：左辺は実際の比較射と unstraightening の射影の合成。
使われ方：Kerodon Example 5.6.2.9（Tag 026S）、coherent な復元の底上の図式。 -/
lemma leftCoherentTransportDirectComparison_projection
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    leftCoherentTransportDirectComparison p ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p) =
      (SSet.uliftFunctor.{u + 1, u}).map p :=
  scaffoldCoherentComparison_projection p

/-- 概要：直接の coherent transport 比較は前合成同値。
方針：選択した底上の比較の同値性を取り出す。
規約：比較射そのものの性質として記録する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、任意の標的への図式の比較。 -/
lemma leftCoherentTransportDirectComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (leftCoherentTransportDirectComparison p) :=
  scaffoldCoherentComparison_isPrecompositionEquivalence p

/-- 概要：直接の coherent transport 比較は全空間の quasicategory の同値。
方針：quasicategory 間の前合成同値から同値の逆データを回収する。
規約：元の E の quasicategory 性は p の left fibration 性からも得られる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な表現の存在方向の全空間での結論。 -/
lemma leftCoherentTransportDirectComparison_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (leftCoherentTransportDirectComparison p) :=
  (leftCoherentTransportDirectComparison_isPrecompositionEquivalence p).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
