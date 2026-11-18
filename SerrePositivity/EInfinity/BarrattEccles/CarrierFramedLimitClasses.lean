module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitHom
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.FrameConeClasses

/-!
# 底の右錐の Hom 比較を元の複体射で正規化する

概要：BM 命題 4.1・Hovey §5.4 の底の Hom 比較で元の射の局所化像を回収する。
方針：実際の重み付き実現の随伴で族を作り、同じ π₀ 比較で計算する。
規約：元の複体射・右 frame・試験始域・底の同型を保持する。
使われ方：一般 homotopy 極限の底の比較の正規化。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：忘却後の計算対象への射から底の右錐の類を作る（Hovey §5.4）。
方針：同じ試験始域と底の計算同型を合成し、実現随伴で族へ移す。
規約：元の複体射を使い、局所化 Hom 同値の逆で類を選ばない。
使われ方：底の右錐の Hom 比較を具体的な複体射で正規化する。 -/
def carrierFramedLimitMapClass (F : K ⥤ (operad A).Algebra) {Y : Complex A}
    (f : Y ⟶ ((framedLimitFunctor A K).obj F).carrier) :
    SSet.π₀ ((carrierFramedLimitConeSpace A K Y).obj F) :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    ((FrameWeightRealization.adjunction Kᵒᵖ (carrierRightFrameDiagram A K F)).homEquiv
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (op (carrierFramedLimitProbe A Y))
      (((carrierFramedLimitProbeComparison A).app Y ≫ f ≫
        (framedLimitCarrierIso A K F).hom).op))
/-- 概要：底の右錐の Hom 比較は元の複体射の局所化像を回収（Hovey §5.4）。
方針：実現随伴の類の計算から試験始域比較と底の計算同型を相殺する。
規約：元の始域複体に cofibrancy を仮定しない。
使われ方：忘却した通常錐の比較射との照合。 -/
lemma carrierFramedLimitHomPiZeroEquiv_mapClass (F : K ⥤ (operad A).Algebra) {Y : Complex A}
    (f : Y ⟶ ((framedLimitFunctor A K).obj F).carrier) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    carrierFramedLimitHomPiZeroEquiv A K F Y (carrierFramedLimitMapClass A K F f) = Q.map f := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let Q := (weakEquivalences (Complex A)).Q
  have : Q.op.IsLocalization (weakEquivalences (Complex A)ᵒᵖ) := by
    rw [weakEquivalences_op]
    infer_instance
  have := carrierFramedLimitProbe_cofibrant A Y
  have : IsFibrant (op (carrierFramedLimitProbe A Y)) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant _
  let p := (carrierFramedLimitProbeComparison A).app Y
  let h := p ≫ f ≫ (framedLimitCarrierIso A K F).hom
  let e := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (carrierRightFrameDiagram A K F) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
    (fun k => carrierRightFrame_cofibrant A (F.obj k.unop))
    (fun k _ _ g => carrierRightFrame_homotopicallyConstant A (F.obj k.unop) g) Q.op
    (op (carrierFramedLimitProbe A Y))
  have hr : e (carrierFramedLimitMapClass A K F f) = Q.op.map h.op :=
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv_class Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
      (carrierRightFrameDiagram A K F) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
      (fun k => carrierRightFrame_cofibrant A (F.obj k.unop))
      (fun k _ _ g => carrierRightFrame_homotopicallyConstant A (F.obj k.unop) g) Q.op h.op
  have : IsIso (Q.map p) := Localization.inverts Q (weakEquivalences (Complex A)) p
    (carrierFramedLimitProbeComparison_quasiIso A Y)
  change (asIso (Q.map p)).inv ≫ (e (carrierFramedLimitMapClass A K F f)).unop ≫
    Q.map (framedLimitCarrierIso A K F).inv = Q.map f
  rw [hr]
  change inv (Q.map p) ≫ Q.map h ≫ Q.map (framedLimitCarrierIso A K F).inv = _
  have hh : h ≫ (framedLimitCarrierIso A K F).inv = p ≫ f := by
    dsimp only [h]
    calc
      (p ≫ f ≫ (framedLimitCarrierIso A K F).hom) ≫ (framedLimitCarrierIso A K F).inv =
          (p ≫ f) ≫ ((framedLimitCarrierIso A K F).hom ≫
            (framedLimitCarrierIso A K F).inv) := by simp only [Category.assoc]
      _ = (p ≫ f) ≫ 𝟙 _ := congrArg (fun z => (p ≫ f) ≫ z)
        (framedLimitCarrierIso A K F).hom_inv_id
      _ = p ≫ f := Category.comp_id _
  rw [← Q.map_comp, hh, Q.map_comp]
  exact IsIso.inv_hom_id_assoc _ _

end SerrePositivity.EInfinity.BarrattEccles
