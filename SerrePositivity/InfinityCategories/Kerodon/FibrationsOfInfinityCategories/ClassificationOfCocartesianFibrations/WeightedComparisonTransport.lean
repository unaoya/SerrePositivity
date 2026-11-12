module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WeightedTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationTransportNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberReflection

/-!
概要：持ち上げた weighted nerve の比較射を介し、係数の射と標的の transport を比較する。
方針：持ち上げた係数輸送と底上の射に関する transport の自然性を合成する。
規約：底は元の nerve の宇宙持ち上げであり、coherent な復元の比較と同じ宇宙に置く。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な Kan 図式とその unstraightening の射への作用の照合。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：持ち上げた係数値から、全空間の比較射の標的 fiber への射。
方針：係数値の標準 fiber 同型と比較射の fiber への作用を合成する。
規約：比較射は持ち上げた底の nerve を厳密に保つ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元の値での比較の射。 -/
noncomputable def uliftWeightedNerveComparisonFiber {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{max u v}}
    (q : E ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve C))
    (h : (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) ⟶ E)
    (hh : h ≫ q = (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)) (c : C) :
    (SSet.uliftFunctor.{v, u}).obj (F.obj c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftWeightedNerveFiberIso.{u, v} F c).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)) q h hh
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))

/-- 概要：持ち上げた係数の射と比較先の transport は fiber の比較射を介して関手同型まで可換。
方針：持ち上げた係数での標準 transport の同定と、全空間の射に関する自然性を合成する。
規約：同型は持ち上げた F(c) から比較先の終点 fiber への射の間で取る。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元で元の Kan 複体の射を回収する。 -/
noncomputable def uliftWeightedNerveComparisonFiber_transportIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{max u v}} (q : E ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve C)) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (h : (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) ⟶ E)
    (hh : h ≫ q = (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F))
    {c d : C} (f : c ⟶ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{v, u}).map (F.map f) ≫ uliftWeightedNerveComparisonFiber F q h hh d)
      (uliftWeightedNerveComparisonFiber F q h hh c ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} (nerve.edgeMk f))) := by
  have e₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftWeightedNerveTransport_coefficientIso.{u, v} F f).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftWeightedNerveFiberIso.{u, v} F d).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)) q h hh
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex d)))
  have e₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationMap_transportIso ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F))
      q h hh (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} (nerve.edgeMk f)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftWeightedNerveFiberIso.{u, v} F c).hom
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at e₀
  exact e₀ ≪≫ e₁

/-- 概要：全空間の前合成同値から、持ち上げた係数と標的 fiber の比較の同値性を得る。
方針：相対逆による fiber 同値の回収に標準 fiber 同型を合成する。
規約：底の持ち上げた nerve は quasicategory。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、選択した復元比較の値での同値性。 -/
lemma uliftWeightedNerveComparisonFiber_isQCatEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{max u v}} (q : E ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve C)) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (h : (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) ⟶ E)
    (hh : h ≫ q = (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F))
    (eh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence h) (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (uliftWeightedNerveComparisonFiber F q h hh c) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftWeightedNerveFiberIso.{u, v} F c)).isQCatEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
      ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)) q h hh eh
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)))

/-- 概要：持ち上げた weighted nerve と同値な標的の transport の同値性は持ち上げた係数の射で判定できる。
方針：全空間の同値から両端の fiber 同値を回収し、transport の自然性に二対三則を使う。
規約：比較射 h は底を保つ前合成同値。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元の transport の同値性を検出する。 -/
lemma uliftWeightedNerveComparison_transport_isQCatEquivalence_iff
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {E : SSet.{max u v}} (q : E ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve C)) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (h : (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) ⟶ E)
    (hh : h ≫ q = (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F))
    (eh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence h) {c d : C} (f : c ⟶ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} (nerve.edgeMk f))) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((SSet.uliftFunctor.{v, u}).map (F.map f)) := by
  have hc := uliftWeightedNerveComparisonFiber_isQCatEquivalence F q h hh eh c
  have hd := uliftWeightedNerveComparisonFiber_isQCatEquivalence F q h hh eh d
  have e := uliftWeightedNerveComparisonFiber_transportIso F q h hh f
  exact ⟨fun he ↦ hd.cancel_right ((hc.comp he).ofFunctorIso e.symm),
    fun he ↦ hc.cancel_left ((he.comp hd).ofFunctorIso e)⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
