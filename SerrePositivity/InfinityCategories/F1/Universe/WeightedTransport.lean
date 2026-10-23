module

public import SerrePositivity.InfinityCategories.F1.Universe.Transport
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveTransport

/-!
概要：持ち上げた weighted nerve の transport を持ち上げた係数の射として回収する。
方針：標準 fiber 同型を持ち上げて fiber の宇宙同型を合成し、係数輸送の prism を移送する。
規約：追加の宇宙 v は任意。
使われ方：Kerodon Corollary 5.6.0.6、元の Kan 値図式の作用を coherent な復元の宇宙で照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：持ち上げた係数値と持ち上げた weighted nerve の fiber の標準同型。
方針：係数値と元の fiber の同型を持ち上げ、fiber の宇宙同型を合成する。
規約：底の頂点は nerveVertex c の ULift。
使われ方：Kerodon Corollary 5.6.0.6、coherent な復元と比較する係数値の表示。 -/
noncomputable def uliftWeightedNerveFiberIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    (SSet.uliftFunctor.{v, u}).obj (F.obj c) ≅
      vertexFiber ((SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F))
        (ULift.up (nerveVertex c)) :=
  (SSet.uliftFunctor.{v, u}).mapIso (weightedNerveFiberIso F c) ≪≫
    uliftVertexFiberIso.{u, v} (weightedNerveProjection F) (nerveVertex c)

/-- 概要：持ち上げた係数の射は持ち上げた weighted nerve の transport の条件を満たす。
方針：係数輸送の証人を宇宙持ち上げし、二つの fiber 同型の合成で表示を揃える。
規約：始域と標的の係数値は同じ宇宙持ち上げを使う。
使われ方：Kerodon Corollary 5.6.0.6、復元の宇宙で使う係数 transport の証人。 -/
lemma uliftWeightedNerveCoefficientTransport_isTransport
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {c d : C} (f : c ⟶ d) :
    IsEdgeTransport ((SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F))
      (uliftTruncatedEdge.{u, v} (nerve.edgeMk f))
      ((uliftWeightedNerveFiberIso.{u, v} F c).inv ≫
        (SSet.uliftFunctor.{v, u}).map (F.map f) ≫ (uliftWeightedNerveFiberIso.{u, v} F d).hom) := by
  have h := IsEdgeTransport.ulift.{u, v} (weightedNerveProjection F) (nerve.edgeMk f)
    (weightedNerveCoefficientTransport_isTransport F f)
  simp only [uliftFiberTransport, weightedNerveCoefficientTransport,
    uliftWeightedNerveFiberIso, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc] at h ⊢
  exact h

/-- 概要：持ち上げた weighted nerve の標準 transport は、係数値で持ち上げた係数の射と関手同型。
方針：持ち上げた係数輸送と標準 transport の一意性を使い、標準 fiber 同型を両側で消去する。
規約：比較先の射は元の F.map f の ULift。
使われ方：Kerodon Corollary 5.6.0.6、coherent な unstraightening と係数の射の比較の始域側。 -/
noncomputable def uliftWeightedNerveTransport_coefficientIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    {c d : C} (f : c ⟶ d) :
    FunctorIso
      ((uliftWeightedNerveFiberIso.{u, v} F c).hom ≫
        edgeTransport ((SSet.uliftFunctor.{v, u}).map (weightedNerveProjection F))
          (uliftTruncatedEdge.{u, v} (nerve.edgeMk f)) ≫
            (uliftWeightedNerveFiberIso.{u, v} F d).inv)
      ((SSet.uliftFunctor.{v, u}).map (F.map f)) := by
  let e := (IsEdgeTransport.functorIso _ _
    (uliftWeightedNerveCoefficientTransport_isTransport.{u, v} F f)
    (edgeTransport_isTransport _ _)).some
  have h := FunctorIso.precomp (FunctorIso.postcomp e.symm (uliftWeightedNerveFiberIso F d).inv)
    (uliftWeightedNerveFiberIso F c).hom
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using h

end SerrePositivity.InfinityCategories
