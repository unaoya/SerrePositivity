module

public import SerrePositivity.EInfinity.ComplexLimits.FramedLimitConeNormalization
public import SerrePositivity.EInfinity.ComplexLimits.FramedLimitHomPiZero

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

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：右錐の元の通常錐の類は同じ図式射の局所化（Hovey §5.4）。
方針：両 frame の類の一致と始域側の計算を使い、試験始域の比較を相殺する。
規約：元の錐の頂点に cofibrancy を仮定しない。
使われ方：導来 Hom 同値の元の錐による正規化。 -/
lemma framedLimitConePiZeroEquiv_coneClass (F : K ⥤ (Complex A)) (c : Cone F) :
    let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let QD := (weakEquivalences (K ⥤ (Complex A))).Q
    framedLimitConePiZeroEquiv A K c.pt F (framedLimitConeClass A K F c) = QD.map c.π := by
  let := projectiveModelCategory A
  let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  let QD := (weakEquivalences (K ⥤ (Complex A))).Q
  let f : (Functor.const K).obj (framedLimitProbe A c.pt) ⟶ F :=
    (Functor.const K).map (framedLimitProbeComparison A c.pt) ≫ c.π
  let e := sourceRightConeComparisonIso A K c.pt F SSet.π₀Functor
    SimplicialModel.PiZeroLocalization.inverts_anodyne
  have hc := sourceRightConeComparisonIso_coneClass A K F c
  have hi : e.inv (framedLimitConeClass A K F c) =
    BarrattEccles.CarrierDiagram.constantDiagramSourceClass A K f := by
    change e.hom (BarrattEccles.CarrierDiagram.constantDiagramSourceClass A K f) = _ at hc
    rw [← hc]
    exact e.toEquiv.symm_apply_apply _
  dsimp only
  change (constantProbeLocalizedIso A K c.pt).inv ≫
    BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv A K (framedLimitProbe A c.pt) F
      (e.inv (framedLimitConeClass A K F c)) ≫ 𝟙 _ = _
  rw [hi, BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv_class]
  dsimp only [f]
  rw [QD.map_comp, Category.comp_id]
  have : IsIso (QD.map ((Functor.const K).map (framedLimitProbeComparison A c.pt))) :=
    (constantProbeLocalizedIso A K c.pt).isIso_hom
  change inv (QD.map ((Functor.const K).map (framedLimitProbeComparison A c.pt))) ≫
    QD.map ((Functor.const K).map (framedLimitProbeComparison A c.pt)) ≫ QD.map c.π = _
  exact IsIso.inv_hom_id_assoc _ _

/-- 概要：導来 Hom 同値は通常錐を元の計算対象への比較に送る（Hovey §5.4）。
方針：同じ右錐の類による左右の局所化 Hom の計算を合成する。
規約：元の coneToFramedLimit と元の図式射の局所化像を保持する。
使われ方：通常の極限比較を持つ右導来関手の普遍性。 -/
lemma framedLimitDerivedHomEquiv_cone (F : K ⥤ (Complex A)) (c : Cone F) :
    let := projectiveModelCategory A
    let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ (Complex A))).Q
    framedLimitDerivedHomEquiv A K c.pt F (QD.map c.π) =
      Q.map (coneToFramedLimit A K F c) := by
  let := projectiveModelCategory A
  let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  dsimp only
  rw [← framedLimitConePiZeroEquiv_coneClass A K F c]
  change framedLimitHomPiZeroEquiv A K c.pt F
    ((framedLimitConePiZeroEquiv A K c.pt F).symm
      (framedLimitConePiZeroEquiv A K c.pt F (framedLimitConeClass A K F c))) = _
  rw [Equiv.symm_apply_apply]
  exact framedLimitHomPiZeroEquiv_coneClass A K F c

end SerrePositivity.EInfinity.ComplexLimits
