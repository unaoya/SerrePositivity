module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.DirectKanUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningCandidate

/-!
概要：直値の straightening 候補の unstraightening は元の left fibration を復元する。
方針：strict transport の復元 span に直値の Kan 図式の比較を合成し、底上の射へ厳密化する。
規約：通常の圏の nerve を底とする。一般の coherent 図式の分類は別に証明する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、straightening の構成方向の全空間比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：元の全空間から直値の straightening 候補の復元への底上の同値射が存在する。
方針：strict transport の復元 span を持ち上げて直値の復元へ合成し、共通の始域を消去する。
規約：底の nerve と元の全空間を u+1 に持ち上げる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、left straightening 候補の復元の存在方向。 -/
lemma exists_leftStraighteningCandidateComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    ∃ f : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCandidate p),
      f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCandidate p) =
        (SSet.uliftFunctor.{u + 1, u}).map p ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f := by
  obtain ⟨Z, t, a, b, ht, ha, hb, ea, eb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.exists_leftStrictTransport_reconstruction_span p
  have : InnerFibration t := ht
  have : Quasicategory Z := quasicategory_of_innerFibration t
  have : Quasicategory E := quasicategory_of_innerFibration p
  let U := SSet.uliftFunctor.{u + 1, u}
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.directKanUnstraighteningComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p)
  have hf : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCandidate p) =
      U.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportWeightedProjection p) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.directKanUnstraighteningComparison_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p)
  have ef : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.directKanUnstraighteningComparison_isPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_leftFibration_comparison_of_span (U.map p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCandidate p)) (U.map t)
    (U.map a) (U.map b ≫ f)
    (by rw [← U.map_comp, ha])
    (by rw [Category.assoc, hf, ← U.map_comp, hb])
    ea.isQCatEquivalence.ulift.isPrecompositionEquivalence
    (eb.isQCatEquivalence.ulift.isPrecompositionEquivalence.comp ef)

/-- 概要：元の left fibration から直値の straightening 候補の復元への実際の比較射。
方針：底上の同値射の存在から選ぶ。
規約：比較射は非計算的。候補図式の値は反転しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、既存の coherent straightening の頂点での復元。 -/
noncomputable def leftStraighteningCandidateComparison
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCandidate p) :=
  (exists_leftStraighteningCandidateComparison p).choose

/-- 概要：直値の straightening 候補の復元比較は底への射影を厳密に保つ。
方針：選択した比較の存在条件を使う。
規約：元の p と同じ底の持ち上げ上の等式。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、元の fibration と復元の底上の比較。 -/
lemma leftStraighteningCandidateComparison_projection
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    leftStraighteningCandidateComparison p ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningCandidate p) =
      (SSet.uliftFunctor.{u + 1, u}).map p :=
  (exists_leftStraighteningCandidateComparison p).choose_spec.1

/-- 概要：直値の straightening 候補の復元比較は前合成同値。
方針：選択した比較の同値条件を使う。
規約：底上の実際の射の性質として述べる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、straightening の構成方向の全空間比較。 -/
lemma leftStraighteningCandidateComparison_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (leftStraighteningCandidateComparison p) :=
  (exists_leftStraighteningCandidateComparison p).choose_spec.2

/-- 概要：直値の straightening 候補の復元比較は quasicategory の同値。
方針：quasicategory 間の前合成同値から逆射のデータを回収する。
規約：元の全空間の quasicategory 性は p の充填性からも得られる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、直値の coherent 表現による復元。 -/
lemma leftStraighteningCandidateComparison_isQCatEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}} [Quasicategory E]
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (leftStraighteningCandidateComparison p) :=
  (leftStraighteningCandidateComparison_isPrecompositionEquivalence p).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
