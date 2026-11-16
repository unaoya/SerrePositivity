module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitConeNormalization
public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitConePiZero
public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitForgetComparison

/-!
# 導来 Hom 同値の元の通常錐による正規化

概要：BM 命題 4.1・Hovey §5.4 の導来 Hom 同値を元の錐からの比較で計算する。
方針：同じ右錐の類から両局所化 Hom の元を回収する。
規約：任意の小図式と元の頂点を使い、追加の cofibrancy は不要。
使われ方：一般 homotopy 極限の元の比較射と導来普遍性の接続。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：右錐の元の通常錐の類は同じ図式射の局所化（Hovey §5.4）。
方針：両 frame の類の一致と始域側の計算を使い、試験始域の比較を相殺する。
規約：元の錐の頂点に cofibrancy を仮定しない。
使われ方：導来 Hom 同値の元の錐による正規化。 -/
lemma carrierFramedLimitConePiZeroEquiv_coneClass (F : K ⥤ (operad A).Algebra) (c : Cone
  ((Diagram.forget A K).obj F)) :
    let := CarrierDiagram.projectiveModelCategory A K
    let QD := (weakEquivalences (K ⥤ Complex A)).Q
    carrierFramedLimitConePiZeroEquiv A K c.pt F (carrierFramedLimitConeClass A K F c) = QD.map
      c.π := by
  let := projectiveModelCategory A
  let := CarrierDiagram.projectiveModelCategory A K
  let QD := (weakEquivalences (K ⥤ Complex A)).Q
  let f : (Functor.const K).obj (carrierFramedLimitProbe A c.pt) ⟶ (Diagram.forget A K).obj F :=
    (Functor.const K).map ((carrierFramedLimitProbeComparison A).app c.pt) ≫ c.π
  let e := carrierSourceRightConeComparisonIso A K c.pt F SSet.π₀Functor
    SimplicialModel.PiZeroLocalization.inverts_anodyne
  have hc := carrierSourceRightConeComparisonIso_coneClass A K F c
  have hi : e.inv (carrierFramedLimitConeClass A K F c) =
    CarrierDiagram.constantDiagramSourceClass A K f := by
    change e.hom (CarrierDiagram.constantDiagramSourceClass A K f) = _ at hc
    rw [← hc]
    exact e.toEquiv.symm_apply_apply _
  dsimp only
  change (carrierConstantProbeLocalizedIso A K c.pt).inv ≫
    CarrierDiagram.constantDiagramSourcePiZeroEquiv A K (carrierFramedLimitProbe A c.pt)
      ((Diagram.forget A K).obj F)
      (e.inv (carrierFramedLimitConeClass A K F c)) ≫ 𝟙 _ = _
  rw [hi, CarrierDiagram.constantDiagramSourcePiZeroEquiv_class]
  dsimp only [f]
  rw [QD.map_comp, Category.comp_id]
  have : IsIso (QD.map ((Functor.const K).map ((carrierFramedLimitProbeComparison A).app c.pt))) :=
    (carrierConstantProbeLocalizedIso A K c.pt).isIso_hom
  change inv (QD.map ((Functor.const K).map ((carrierFramedLimitProbeComparison A).app c.pt))) ≫
    QD.map ((Functor.const K).map ((carrierFramedLimitProbeComparison A).app c.pt)) ≫ QD.map c.π = _
  exact IsIso.inv_hom_id_assoc _ _

/-- 概要：導来 Hom 同値は通常錐を元の計算対象への比較に送る（Hovey §5.4）。
方針：同じ右錐の類による左右の局所化 Hom の計算を合成する。
規約：元の carrierConeToFramedLimit と元の図式射の局所化像を保持する。
使われ方：通常の極限比較を持つ右導来関手の普遍性。 -/
lemma carrierFramedLimitDerivedHomEquiv_cone (F : K ⥤ (operad A).Algebra) (c : Cone
  ((Diagram.forget A K).obj F)) :
    let := projectiveModelCategory A
    let := CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ Complex A)).Q
    carrierFramedLimitDerivedHomEquiv A K c.pt F (QD.map c.π) =
      Q.map (carrierConeToFramedLimit A K F c) := by
  let := projectiveModelCategory A
  let := CarrierDiagram.projectiveModelCategory A K
  dsimp only
  rw [← carrierFramedLimitConePiZeroEquiv_coneClass A K F c]
  change carrierFramedLimitHomPiZeroEquiv A K F c.pt
    ((carrierFramedLimitConePiZeroEquiv A K c.pt F).symm
      (carrierFramedLimitConePiZeroEquiv A K c.pt F (carrierFramedLimitConeClass A K F c))) = _
  rw [Equiv.symm_apply_apply]
  exact carrierFramedLimitHomPiZeroEquiv_coneClass A K F c

/-- 概要：忘却した E 代数錐は元の代数比較の底の局所化像へ移る（BM 命題 4.1）。
方針：底の通常錐の正規化と元の比較射の忘却との一致を合成する。
規約：元の coneToFramedLimit の同じ射を使う。
使われ方：元の極限比較と底の導来極限比較の接続。 -/
lemma carrierFramedLimitDerivedHomEquiv_forgetCone (F : K ⥤ (operad A).Algebra)
    (c : Cone F) :
    let := projectiveModelCategory A
    let := CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ Complex A)).Q
    carrierFramedLimitDerivedHomEquiv A K c.pt.carrier F
        (QD.map ((Operad.Algebra.forget (operad A)).mapCone c).π) =
      Q.map (coneToFramedLimit A K F c).hom := by
  let := projectiveModelCategory A
  let := CarrierDiagram.projectiveModelCategory A K
  dsimp only
  exact (carrierFramedLimitDerivedHomEquiv_cone A K F
    ((Operad.Algebra.forget (operad A)).mapCone c)).trans
      (congrArg ((weakEquivalences (Complex A)).Q.map)
        (carrierConeToFramedLimit_forget A K F c))

end SerrePositivity.EInfinity.BarrattEccles
