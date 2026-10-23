module

public import SerrePositivity.InfinityCategories.F1.Weighted.NerveTransportPrism
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveLeftFibration
public import SerrePositivity.InfinityCategories.F1.Transport.EdgeTransport

/-!
概要：Kan 値図式の射は weighted nerve の fiber 間の transport を表す。
方針：明示的な係数輸送の prism を fiber の標準同型で移送し、transport の一意性を使う。
規約：同型は fiber 内の関手同型。係数の射は任意で、可逆性は要求しない。
使われ方：Kerodon §5.3.3、Corollary 5.6.0.6、coherent な復元の作用を元の Kan 複体の射と照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：weighted nerve の標準 fiber 同型を全空間へ含めると係数の定値包含。
方針：標準 fiber 比較の持ち上げの定義を計算する。
規約：係数の Kan 性は不要。
使われ方：Kerodon §5.3.3、transport prism の二端点を fiber 内へ移す式。 -/
lemma weightedNerveFiberIso_hom_ι {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    (weightedNerveFiberIso F c).hom ≫
      vertexFiberι (weightedNerveProjection F) (nerveVertex c) =
        weightedNerveConstantLift F c := rfl

/-- 概要：係数の定値包含に fiber 同型の逆射を前合成すると fiber の包含。
方針：標準同型の往復を消去する。
規約：係数の Kan 性は不要。
使われ方：Kerodon §5.3.3、始域 fiber 全体を始点とする prism の初期値。 -/
lemma weightedNerveFiberIso_inv_constantLift {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    (weightedNerveFiberIso F c).inv ≫ weightedNerveConstantLift F c =
      vertexFiberι (weightedNerveProjection F) (nerveVertex c) := by
  rw [← weightedNerveFiberIso_hom_ι, Iso.inv_hom_id_assoc]

/-- 概要：係数の射を標準 fiber 同型で移送して fiber 間の射にする。
方針：始域の同型の逆、係数の射、標的の同型を合成する。
規約：底の辺は元の f の nerve の辺。
使われ方：Kerodon §5.3.3、weighted nerve の transport の具体的な候補。 -/
noncomputable def weightedNerveCoefficientTransport {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    vertexFiber (weightedNerveProjection F) (nerveVertex c) ⟶
      vertexFiber (weightedNerveProjection F) (nerveVertex d) :=
  (weightedNerveFiberIso F c).inv ≫ F.map f ≫ (weightedNerveFiberIso F d).hom

/-- 概要：係数の射の fiber 間への移送は f の辺に沿う transport の条件を満たす。
方針：明示的な係数輸送の prism を始域の fiber 同型の逆で制限する。
規約：全ての垂直辺の cocartesian 性は weighted nerve の left fibration 性による。
使われ方：Kerodon §5.3.3、Corollary 5.6.0.6、復元の作用の係数での同定。 -/
lemma weightedNerveCoefficientTransport_isTransport {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] {c d : C} (f : c ⟶ d) :
    IsEdgeTransport (weightedNerveProjection F) (nerve.edgeMk f)
      (weightedNerveCoefficientTransport F f) := by
  refine ⟨(Δ[1] ◁ (weightedNerveFiberIso F c).inv) ≫ weightedNerveTransportPrism F f,
    ?_, ?_, ?_, fun _ ↦ isCocartesianEdge_of_leftFibration (weightedNerveProjection F) _⟩
  · rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      weightedNerveTransportPrism_zero, weightedNerveFiberIso_inv_constantLift]
    rfl
  · rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      weightedNerveTransportPrism_one, weightedNerveCoefficientTransport,
      Category.assoc, Category.assoc]
    exact congrArg (fun z ↦ (weightedNerveFiberIso F c).inv ≫ F.map f ≫ z)
      (weightedNerveFiberIso_hom_ι F d).symm
  · rw [Category.assoc, weightedNerveTransportPrism_projection, ← Category.assoc,
      whiskerLeft_fst]
    rfl

/-- 概要：標準 transport は fiber の同型で元の係数の射へ戻すと関手同型。
方針：係数輸送と標準 transport の一意性を使い、両側の fiber 同型を消去する。
規約：比較は係数値 F(c) から F(d) への関手間の同型。
使われ方：Kerodon Proposition 5.2.2.8、Corollary 5.6.0.6、Kan 値図式の射の回収。 -/
noncomputable def weightedNerveTransport_coefficientIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] {c d : C} (f : c ⟶ d) :
    FunctorIso
      ((weightedNerveFiberIso F c).hom ≫
        edgeTransport (weightedNerveProjection F) (nerve.edgeMk f) ≫
          (weightedNerveFiberIso F d).inv)
      (F.map f) := by
  let e := (IsEdgeTransport.functorIso (weightedNerveProjection F) (nerve.edgeMk f)
    (weightedNerveCoefficientTransport_isTransport F f)
    (edgeTransport_isTransport (weightedNerveProjection F) (nerve.edgeMk f))).some
  have h := FunctorIso.precomp (FunctorIso.postcomp e.symm (weightedNerveFiberIso F d).inv)
    (weightedNerveFiberIso F c).hom
  simpa only [weightedNerveCoefficientTransport, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using h

/-- 概要：weighted nerve の辺の標準 transport が同値である条件は、係数の射の同値性と一致する。
方針：係数での関手同型と二つの fiber 同型に同値の二対三則を適用する。
規約：係数の射 f の可逆性を仮定しない判定。
使われ方：Kerodon Corollary 5.6.0.6、coherent な復元との比較で射の同値性を検出する。 -/
lemma weightedNerveTransport_isQCatEquivalence_iff {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] {c d : C} (f : c ⟶ d) :
    IsQCatEquivalence (edgeTransport (weightedNerveProjection F) (nerve.edgeMk f)) ↔
      IsQCatEquivalence (F.map f) := by
  have ec := (qCatEquivalenceOfIso (weightedNerveFiberIso F c)).isQCatEquivalence
  have ed := (qCatEquivalenceOfIso (weightedNerveFiberIso F d).symm).isQCatEquivalence
  have e := weightedNerveTransport_coefficientIso F f
  constructor
  · intro h
    exact (ec.comp (h.comp ed)).ofFunctorIso e
  · intro h
    exact ec.cancel_left (ed.cancel_right (h.ofFunctorIso e.symm))

end SerrePositivity.InfinityCategories
