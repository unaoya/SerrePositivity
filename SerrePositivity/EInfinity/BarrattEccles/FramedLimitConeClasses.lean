module

public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitComparison
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitHomPiZero
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
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：通常の錐は既存の右 frame の錐空間の同じ類を与える（Hovey §5.4）。
方針：元の strictConeWeightedFamily に同じ試験始域の比較を前合成する。
規約：既存の右錐空間と試験始域を変更しない。
使われ方：元の通常の錐の具体的な右側の代表。 -/
def framedLimitConeClass (F : K ⥤ (operad A).Algebra) (c : Cone F) :
    SSet.π₀ ((framedLimitConeSpace A K c.pt).obj F) :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (strictConeWeightedFamily A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c ≫
      (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).map
        (framedLimitProbeComparison A c.pt).op)

/-- 概要：元の右錐の類は coneToFramedLimit の同じ局所化射（Hovey §5.4）。
方針：実現随伴からの錐の類の式を反対化し、試験始域比較の順逆を相殺する。
規約：元の錐の頂点の cofibrancy は仮定しない。
使われ方：具体的な錐比較と導来 Hom 同値の正規化。 -/
lemma framedLimitHomPiZeroEquiv_coneClass (F : K ⥤ (operad A).Algebra) (c : Cone F) :
    let := modelCategory A
    let Q := (weakEquivalences (operad A).Algebra).Q
    framedLimitHomPiZeroEquiv A K c.pt F (framedLimitConeClass A K F c) =
      Q.map (coneToFramedLimit A K F c) := by
  let := modelCategory A
  let Q := (weakEquivalences (operad A).Algebra).Q
  have : Q.op.IsLocalization (weakEquivalences (operad A).Algebraᵒᵖ) := by
    rw [weakEquivalences_op]
    infer_instance
  have := framedLimitProbe_cofibrant A c.pt
  have : IsFibrant (op (framedLimitProbe A c.pt)) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant _
  let p := framedLimitProbeComparison A c.pt
  let f := p ≫ coneToFramedLimit A K F c
  let e := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (rightFrameDiagram A K F) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
    (fun k => rightFrame_cofibrant A (F.obj k.unop))
    (fun k _ _ g => rightFrame_homotopicallyConstant A (F.obj k.unop) g) Q.op
    (op (framedLimitProbe A c.pt))
  have hfam : strictConeWeightedFamily A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c ≫
        (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).map p.op =
      (FrameWeightRealization.adjunction Kᵒᵖ (rightFrameDiagram A K F)).homEquiv
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (op (framedLimitProbe A c.pt)) f.op := by
    have h := weightedCotensorHomEquiv_precomp A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) p
      (coneToFramedLimit A K F c)
    have hc : weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c.pt
        (coneToFramedLimit A K F c) =
      strictConeWeightedFamily A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c :=
      (weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c.pt).apply_symm_apply _
    have hh := (h.trans (congrArg (fun s => s ≫
      (FrameWeightRealization.hom Kᵒᵖ (rightFrameDiagram A K F)).map p.op) hc)).symm
    simpa only [weightedCotensorHomEquiv, Equiv.trans_apply, Equiv.coe_fn_mk] using hh
  have he : e (framedLimitConeClass A K F c) = Q.op.map f.op := by
    change e (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) _) = _
    rw [hfam]
    exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv_class Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
      (rightFrameDiagram A K F) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
      (fun k => rightFrame_cofibrant A (F.obj k.unop))
      (fun k _ _ g => rightFrame_homotopicallyConstant A (F.obj k.unop) g) Q.op f.op
  have hu : (e (framedLimitConeClass A K F c)).unop = Q.map f :=
    congrArg (fun g : Q.op.obj ((FrameWeightRealization.functor Kᵒᵖ
        (rightFrameDiagram A K F)).obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)) ⟶
      Q.op.obj (op (framedLimitProbe A c.pt)) => g.unop) he
  have : IsIso (Q.map p) := Localization.inverts Q (weakEquivalences (operad A).Algebra) _
    (framedLimitProbeComparison_quasiIso A c.pt)
  change (asIso (Q.map p)).inv ≫ (e (framedLimitConeClass A K F c)).unop ≫ 𝟙 _ = _
  refine (congrArg (fun g : Q.obj (framedLimitProbe A c.pt) ⟶
      Q.obj ((framedLimitFunctor A K).obj F) => (asIso (Q.map p)).inv ≫ g ≫ 𝟙 _) hu).trans ?_
  dsimp only [f]
  rw [Q.map_comp, Category.comp_id]
  change inv (Q.map p) ≫ Q.map p ≫ Q.map (coneToFramedLimit A K F c) =
    Q.map (coneToFramedLimit A K F c)
  exact IsIso.inv_hom_id_assoc _ _

end SerrePositivity.EInfinity.BarrattEccles
