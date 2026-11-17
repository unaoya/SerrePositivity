module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitComparison
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.RealizationCoefficientMap

/-!
# 通常の E 代数錐の比較と底の比較の整合性

概要：BM 命題 4.1・Hovey §5.4 の同じ通常錐の比較射を忘却後に照合する。
方針：元の実現随伴の単体の式と Kan 拡張保存同型の単位整合を使う。
規約：既存の底の同型と元の E 代数比較射を保持する。
使われ方：底の一般右導来極限比較の正規化。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

attribute [local irreducible] rightFrameFamily
attribute [local implicit_reducible] rightFrameDiagram carrierRightFrameDiagram

/-- 概要：底の実現随伴は元の随伴の各単体を忘却した射（Hovey §5.4）。
方針：保存同型の自然性と元の Kan 単位の整合を各単体で合成する。
規約：重みも元の代数射も任意で、元の保存同型を使う。
使われ方：忘却した通常錐の両比較の厳密な一致。 -/
lemma weightedCotensorCarrierHomEquiv_app (F : K ⥤ (operad A).Algebra)
    (W : K ⥤ SSet.{u}) {Y : (operad A).Algebra}
    (f : Y ⟶ (weightedCotensor A K F).obj (op W))
    (k : Kᵒᵖᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (x : (((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).obj W).obj k).obj n) :
    ((((FrameWeightRealization.adjunction Kᵒᵖ (carrierRightFrameDiagram A K F)).homEquiv
      ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).obj W) (op Y.carrier)
        (f.hom ≫ (weightedCotensorCarrierIso A K F W).hom).op).app k).app n) x =
      (Operad.Algebra.forget (operad A)).op.map
        ((((weightedCotensorHomEquiv A K F W Y f).app k).app n) x) := by
  let U := Operad.Algebra.forget (operad A)
  have : U.IsRightAdjoint := (operad A).freeAlgebraAdjunction.isRightAdjoint
  let S := FrameWeightRealization.source Kᵒᵖ (rightFrameDiagram A K F)
  let V := (FrameWeightRealization.weightsEquivalence Kᵒᵖ).functor.obj
    ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).obj W)
  let i := U.op.leftKanExtensionCompIsoOfPreserves S uliftYoneda.{u,u,u}
  let rx : uliftYoneda.{u,u,u}.obj (k.unop, n.unop) ⟶ V := uliftYonedaEquiv.symm x
  have hn := i.inv.naturality rx
  have hu := U.op.leftKanExtensionCompIsoOfPreserves_inv_fac_app S
    uliftYoneda.{u,u,u} (k.unop, n.unop)
  change ((((FrameWeightRealization.adjunction Kᵒᵖ (carrierRightFrameDiagram A K F)).homEquiv
    ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).obj W) (op Y.carrier) (_ ≫ U.op.map f.op)).app k).app n) x =
    U.op.map (((((FrameWeightRealization.adjunction Kᵒᵖ (rightFrameDiagram A K F)).homEquiv
      ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights K).obj W) (op Y) f.op).app k).app n) x)
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationHomEquiv_app, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationHomEquiv_app]
  simp only [Functor.map_comp]
  change (uliftYoneda.leftKanExtensionUnit (S ⋙ U.op)).app (k.unop, n.unop) ≫
      (uliftYoneda.leftKanExtension (S ⋙ U.op)).map rx ≫ i.inv.app V ≫ U.op.map f.op =
    U.op.map ((uliftYoneda.leftKanExtensionUnit S).app (k.unop, n.unop)) ≫
      U.op.map ((uliftYoneda.leftKanExtension S).map rx) ≫ U.op.map f.op
  rw [← Category.assoc ((uliftYoneda.leftKanExtension (S ⋙ U.op)).map rx), hn]
  simpa only [Category.assoc, Functor.comp_map] using
    congrArg (fun z => z ≫ U.op.map ((uliftYoneda.leftKanExtension S).map rx) ≫
      U.op.map f.op) hu

/-- 概要：忘却した通常錐の底の比較は元の E 代数比較の底（BM 命題 4.1）。
方針：同じ随伴の各単体の像を比較し、底の保存同型の順逆を相殺する。
規約：元の coneToFramedLimit と既存の framedLimitCarrierIso を使う。
使われ方：通常の極限比較を忘却した同じ射による導来比較。 -/
lemma carrierConeToFramedLimit_forget (F : K ⥤ (operad A).Algebra) (c : Cone F) :
    carrierConeToFramedLimit A K F ((Operad.Algebra.forget (operad A)).mapCone c) =
      (coneToFramedLimit A K F c).hom := by
  let U := Operad.Algebra.forget (operad A)
  let d : Cone ((Diagram.forget A K).obj F) := U.mapCone c
  let f := coneToFramedLimit A K F c
  let i := framedLimitCarrierIso A K F
  let e := (FrameWeightRealization.adjunction Kᵒᵖ (carrierRightFrameDiagram A K F)).homEquiv
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (op c.pt.carrier)
  let s := carrierStrictConeWeightedFamily A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) d
  have hc : weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c.pt f =
      strictConeWeightedFamily A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c :=
    (weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c.pt).apply_symm_apply _
  have hfam : e (f.hom ≫ i.hom).op = s := by
    ext k n x
    exact (weightedCotensorCarrierHomEquiv_app A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) f k n x).trans
      (congrArg (fun t => U.op.map (((t.app k).app n) x)) hc)
  have he : (f.hom ≫ i.hom).op = e.symm s := by
    simpa only [Equiv.symm_apply_apply] using congrArg e.symm hfam
  change (e.symm s).unop ≫ i.inv = f.hom
  calc
    _ = (f.hom ≫ i.hom) ≫ i.inv := congrArg (fun t => t.unop ≫ i.inv) he.symm
    _ = f.hom := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.EInfinity.BarrattEccles
