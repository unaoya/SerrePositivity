module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.FrameConeClasses

/-!
# 通常の錐が与える実際の右 frame の錐の類

概要：BM 命題 4.1・Hovey §5.4 の通常の錐の右 frame の類を正規化する。
方針：同じ試験始域の比較を前合成し、実現随伴からの錐の類の計算を使う。
規約：元の coneToFramedLimit と同じ重み・右 frame・射を使う。
使われ方：元の通常の錐と導来 Hom 同値の整合性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：通常の錐は既存の右 frame の錐空間の同じ類を与える（Hovey §5.4）。
方針：元の strictConeWeightedFamily に同じ試験始域の比較を前合成する。
規約：既存の右錐空間と試験始域を変更しない。
使われ方：元の通常の錐の具体的な右側の代表。 -/
def carrierFramedLimitConeClass (F : K ⥤ (operad A).Algebra) (c : Cone ((Diagram.forget A K).obj
  F)) :
    SSet.π₀ ((carrierFramedLimitConeSpace A K c.pt).obj F) :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (carrierStrictConeWeightedFamily A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c ≫
      (FrameWeightRealization.hom Kᵒᵖ (carrierRightFrameDiagram A K F)).map
        ((carrierFramedLimitProbeComparison A).app c.pt).op)

/-- 概要：通常錐の類は実際の底の比較射から作った類に一致（Hovey §5.4）。
方針：実現随伴の始域自然性と同じ底の計算同型の順逆を相殺する。
規約：類を抽象同値の逆から選ばない。
使われ方：元の比較射の局所化像を回収する。 -/
lemma carrierFramedLimitConeClass_eq_mapClass (F : K ⥤ (operad A).Algebra)
    (c : Cone ((Diagram.forget A K).obj F)) :
    carrierFramedLimitConeClass A K F c =
      carrierFramedLimitMapClass A K F (carrierConeToFramedLimit A K F c) := by
  let adj := FrameWeightRealization.adjunction Kᵒᵖ (carrierRightFrameDiagram A K F)
  let W := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K
  let s := carrierStrictConeWeightedFamily A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c
  let h := (adj.homEquiv W (op c.pt)).symm s
  let p := (carrierFramedLimitProbeComparison A).app c.pt
  have hc : (carrierConeToFramedLimit A K F c) ≫
      (framedLimitCarrierIso A K F).hom = h.unop := by
    change (h.unop ≫ (framedLimitCarrierIso A K F).inv) ≫
      (framedLimitCarrierIso A K F).hom = h.unop
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := adj.homEquiv_naturality_right h p.op
  have hs : adj.homEquiv W (op c.pt) h = s :=
    (adj.homEquiv W (op c.pt)).apply_symm_apply s
  change _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖᵒᵖ W (s ≫ _ ) =
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖᵒᵖ W
      (adj.homEquiv W (op (carrierFramedLimitProbe A c.pt))
        (p ≫ carrierConeToFramedLimit A K F c ≫ (framedLimitCarrierIso A K F).hom).op)
  rw [hc]
  exact congrArg (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖᵒᵖ W)
    ((congrArg (fun z => z ≫ ((FrameWeightRealization.hom Kᵒᵖ (carrierRightFrameDiagram A K
      F)).map p.op)) hs).symm.trans hn.symm)

/-- 概要：底の通常錐の類から元の比較射の局所化像を回収（Hovey §5.4）。
方針：同じ随伴族の一致と底の射の類の正規化を合成する。
規約：元の複体の cofibrancy は要求しない。
使われ方：底の導来 Hom 同値の通常錐による正規化。 -/
lemma carrierFramedLimitHomPiZeroEquiv_coneClass (F : K ⥤ (operad A).Algebra)
    (c : Cone ((Diagram.forget A K).obj F)) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    carrierFramedLimitHomPiZeroEquiv A K F c.pt (carrierFramedLimitConeClass A K F c) =
      Q.map (carrierConeToFramedLimit A K F c) := by
  rw [carrierFramedLimitConeClass_eq_mapClass]
  exact carrierFramedLimitHomPiZeroEquiv_mapClass A K F _

end SerrePositivity.EInfinity.BarrattEccles
