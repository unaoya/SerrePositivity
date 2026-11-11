module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Transport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveTransport

/-!
概要：持ち上げた weighted nerve の transport を持ち上げた係数の射として回収する。
方針：標準 fiber 同型を持ち上げて fiber の宇宙同型を合成し、係数輸送の prism を移送する。
規約：追加の宇宙 v は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、元の Kan 値図式の作用を coherent な復元の宇宙で照合する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：持ち上げた係数値と持ち上げた weighted nerve の fiber の標準同型。
方針：係数値と元の fiber の同型を持ち上げ、fiber の宇宙同型を合成する。
規約：底の頂点は nerveVertex c の ULift。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元と比較する係数値の表示。 -/
noncomputable def uliftWeightedNerveFiberIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    (SSet.uliftFunctor.{v, u}).obj (F.obj c) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F))
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) :=
  (SSet.uliftFunctor.{v, u}).mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberIso F c) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftVertexFiberIso.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)

/-- 概要：持ち上げた係数の射は持ち上げた weighted nerve の transport の条件を満たす。
方針：係数輸送の証人を宇宙持ち上げし、二つの fiber 同型の合成で表示を揃える。
規約：始域と標的の係数値は同じ宇宙持ち上げを使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、復元の宇宙で使う係数 transport の証人。 -/
lemma uliftWeightedNerveCoefficientTransport_isTransport
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {c d : C} (f : c ⟶ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} (nerve.edgeMk f))
      ((uliftWeightedNerveFiberIso.{u, v} F c).inv ≫
        (SSet.uliftFunctor.{v, u}).map (F.map f) ≫ (uliftWeightedNerveFiberIso.{u, v} F d).hom) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsEdgeTransport.ulift.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (nerve.edgeMk f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficientTransport_isTransport F f)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFiberTransport, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficientTransport,
    uliftWeightedNerveFiberIso, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc] at h ⊢
  exact h

/-- 概要：持ち上げた weighted nerve の標準 transport は、係数値で持ち上げた係数の射と関手同型。
方針：持ち上げた係数輸送と標準 transport の一意性を使い、標準 fiber 同型を両側で消去する。
規約：比較先の射は元の F.map f の ULift。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な unstraightening と係数の射の比較の始域側。 -/
noncomputable def uliftWeightedNerveTransport_coefficientIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {c d : C} (f : c ⟶ d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((uliftWeightedNerveFiberIso.{u, v} F c).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} (nerve.edgeMk f)) ≫
            (uliftWeightedNerveFiberIso.{u, v} F d).inv)
      ((SSet.uliftFunctor.{v, u}).map (F.map f)) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport.functorIso _ _
    (uliftWeightedNerveCoefficientTransport_isTransport.{u, v} F f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport _ _)).some
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.symm (uliftWeightedNerveFiberIso F d).inv)
    (uliftWeightedNerveFiberIso F c).hom
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
