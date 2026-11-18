module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitComparison
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitHomPiZero
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

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra _root_.Opposite
open _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：通常の錐は既存の右 frame の錐空間の同じ類を与える（Hovey §5.4）。
方針：元の strictConeWeightedFamily に同じ試験始域の比較を前合成する。
規約：既存の右錐空間と試験始域を変更しない。
使われ方：元の通常の錐の具体的な右側の代表。 -/
def framedLimitConeClass (F : K ⥤ (Complex A)) (c : Cone F) :
    SSet.π₀ ((_root_.SerrePositivity.ComplexLimits.framedLimitConeSpace A K c.pt).obj F) :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (_root_.SerrePositivity.ComplexLimits.strictConeWeightedFamily A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c ≫
      (FrameWeightRealization.hom Kᵒᵖ (_root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F)).map
        (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A c.pt).op)

/-- 概要：元の右錐の類は coneToFramedLimit の同じ局所化射（Hovey §5.4）。
方針：実現随伴からの錐の類の式を反対化し、試験始域比較の順逆を相殺する。
規約：元の錐の頂点の cofibrancy は仮定しない。
使われ方：具体的な錐比較と導来 Hom 同値の正規化。 -/
lemma framedLimitHomPiZeroEquiv_coneClass (F : K ⥤ (Complex A)) (c : Cone F) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    _root_.SerrePositivity.ComplexLimits.framedLimitHomPiZeroEquiv A K c.pt F (_root_.SerrePositivity.ComplexLimits.framedLimitConeClass A K F c) =
      Q.map (_root_.SerrePositivity.ComplexLimits.coneToFramedLimit A K F c) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let Q := (weakEquivalences (Complex A)).Q
  have : Q.op.IsLocalization (weakEquivalences (Complex A)ᵒᵖ) := by
    rw [weakEquivalences_op]
    infer_instance
  have := _root_.SerrePositivity.ComplexLimits.framedLimitProbe_cofibrant A c.pt
  have : IsFibrant (op (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A c.pt)) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant _
  let p := _root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A c.pt
  let f := p ≫ _root_.SerrePositivity.ComplexLimits.coneToFramedLimit A K F c
  let e := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (_root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
    (fun k => _root_.SerrePositivity.ComplexLimits.rightFrame_cofibrant A (F.obj k.unop))
    (fun k _ _ g => _root_.SerrePositivity.ComplexLimits.rightFrame_homotopicallyConstant A (F.obj k.unop) g) Q.op
    (op (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A c.pt))
  have hfam : _root_.SerrePositivity.ComplexLimits.strictConeWeightedFamily A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c ≫
        (FrameWeightRealization.hom Kᵒᵖ (_root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F)).map p.op =
      (FrameWeightRealization.adjunction Kᵒᵖ (_root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F)).homEquiv
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) (op (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A c.pt)) f.op := by
    have h := _root_.SerrePositivity.ComplexLimits.weightedCotensorHomEquiv_precomp A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) p
      (_root_.SerrePositivity.ComplexLimits.coneToFramedLimit A K F c)
    have hc : _root_.SerrePositivity.ComplexLimits.weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c.pt
        (_root_.SerrePositivity.ComplexLimits.coneToFramedLimit A K F c) =
      _root_.SerrePositivity.ComplexLimits.strictConeWeightedFamily A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c :=
      (_root_.SerrePositivity.ComplexLimits.weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) c.pt).apply_symm_apply _
    have hh := (h.trans (congrArg (fun s => s ≫
      (FrameWeightRealization.hom Kᵒᵖ (_root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F)).map p.op) hc)).symm
    simpa only [_root_.SerrePositivity.ComplexLimits.weightedCotensorHomEquiv, Equiv.trans_apply, Equiv.coe_fn_mk] using hh
  have he : e (_root_.SerrePositivity.ComplexLimits.framedLimitConeClass A K F c) = Q.op.map f.op := by
    change e (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneClass Kᵒᵖᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K) _) = _
    rw [hfam]
    exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv_class Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
      (_root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
      (fun k => _root_.SerrePositivity.ComplexLimits.rightFrame_cofibrant A (F.obj k.unop))
      (fun k _ _ g => _root_.SerrePositivity.ComplexLimits.rightFrame_homotopicallyConstant A (F.obj k.unop) g) Q.op f.op
  have hu : (e (_root_.SerrePositivity.ComplexLimits.framedLimitConeClass A K F c)).unop = Q.map f :=
    congrArg (fun g : Q.op.obj ((FrameWeightRealization.functor Kᵒᵖ
        (_root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F)).obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)) ⟶
      Q.op.obj (op (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A c.pt)) => g.unop) he
  have : IsIso (Q.map p) := Localization.inverts Q (weakEquivalences (Complex A)) _
    (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison_quasiIso A c.pt)
  change (asIso (Q.map p)).inv ≫ (e (_root_.SerrePositivity.ComplexLimits.framedLimitConeClass A K F c)).unop ≫ 𝟙 _ = _
  refine (congrArg (fun g : Q.obj (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A c.pt) ⟶
      Q.obj ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).obj F) => (asIso (Q.map p)).inv ≫ g ≫ 𝟙 _) hu).trans ?_
  dsimp only [f]
  rw [Q.map_comp, Category.comp_id]
  change inv (Q.map p) ≫ Q.map p ≫ Q.map (_root_.SerrePositivity.ComplexLimits.coneToFramedLimit A K F c) =
    Q.map (_root_.SerrePositivity.ComplexLimits.coneToFramedLimit A K F c)
  exact IsIso.inv_hom_id_assoc _ _

end SerrePositivity.ComplexLimits
