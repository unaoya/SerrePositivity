module

public import SerrePositivity.KST.DerivedBlowup.AdjointComparisonCoherence
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComparisonCoherence

/-!
概要：KST §3.1 の正規表示の canonical な導来係数拡大比較の単位・合成条件。
方針：標準導来制限同型から左随伴一意性で係数拡大同型を指定し、随伴で整合性を移す。
規約：比較射と標準同型の両方を構成済みの経路に固定する。
使われ方：正規表示の cartesian 図式の coherent な導来係数拡大側の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Functor
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：正規表示の恒等包含に沿う導来係数拡大の標準単位同型。
方針：標準導来制限単位同型に対応する左随伴の一意性を使う。
規約：KST §3.1。使われ方：canonical な係数拡大比較の単位条件。 -/
abbrev diagramAlgebraDerivedExtensionIdIso (i : J) :=
  adjointComparisonIdIso
    (dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
      (AlgebraVertex (F.obj i))ᵒᵖ (diagramAlgebraVertexTransition F (le_refl i)).op)
    (diagramAlgebraDerivedRestrictionIdIso F i)

/-- 概要：正規表示の二段の導来係数拡大から直接係数拡大への標準同型。
方針：標準導来制限合成同型に対応する左随伴の一意性を使う。
規約：KST §3.1。使われ方：canonical な係数拡大比較の三重条件。 -/
abbrev diagramAlgebraDerivedExtensionCompIso {i j k : J} (h : i ≤ j) (g : j ≤ k) :=
  adjointComparisonCompIso
    (dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
      (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op)
    (dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj j))ᵒᵖ
      (AlgebraVertex (F.obj k))ᵒᵖ (diagramAlgebraVertexTransition F g).op)
    (dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
      (AlgebraVertex (F.obj k))ᵒᵖ (diagramAlgebraVertexTransition F (h.trans g)).op)
    (diagramAlgebraDerivedRestrictionCompIso F h g)

set_option maxHeartbeats 2000000 in
-- 指定 graph 随伴と標準単位比較の Hom 同値を照合するために必要。
/-- 概要：恒等包含の指定導来係数拡大比較は標準単位同型の成分。
方針：随伴像の公式と指定導来制限比較の単位条件を一般の随伴計算へ送る。
規約：KST §3.1。使われ方：指定比較の単位条件と恒等包含での可逆性。 -/
theorem diagramAlgebraDerivedExtensionComparison_id (i : J) (X : DerivedAllDiagramModules F) :
    diagramAlgebraDerivedExtensionComparison F (le_refl i) X =
      (diagramAlgebraDerivedExtensionIdIso F i).hom.app
        ((diagramAlgebraDerivedEvaluation F i).obj X) := by
  apply adjointComparison_id
    (dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
      (AlgebraVertex (F.obj i))ᵒᵖ (diagramAlgebraVertexTransition F (le_refl i)).op)
    (diagramAlgebraDerivedRestrictionIdIso F i)
  rw [diagramAlgebraDerivedExtensionComparison_adjunct]
  exact diagramAlgebraDerivedRestrictionComparison_id F i X

set_option maxHeartbeats 2000000 in
-- 三つの指定 graph 随伴と標準合成同型の型を照合するために必要。
/-- 概要：二段の指定導来係数拡大比較は標準合成同型を介して直接比較に一致する。
方針：三つの指定比較の随伴像を計算し、制限側の三重条件へ戻す。
規約：KST §3.1。使われ方：canonical な cartesian 比較の三重整合性。 -/
theorem diagramAlgebraDerivedExtensionComparison_comp {i j k : J} (h : i ≤ j) (g : j ≤ k)
    (X : DerivedAllDiagramModules F) :
    (diagramAlgebraDerivedExtension F g).map (diagramAlgebraDerivedExtensionComparison F h X) ≫
        diagramAlgebraDerivedExtensionComparison F g X =
      (diagramAlgebraDerivedExtensionCompIso F h g).hom.app
        ((diagramAlgebraDerivedEvaluation F i).obj X) ≫
      diagramAlgebraDerivedExtensionComparison F (h.trans g) X := by
  apply adjointComparison_comp
    (dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
      (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op)
    (dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj j))ᵒᵖ
      (AlgebraVertex (F.obj k))ᵒᵖ (diagramAlgebraVertexTransition F g).op)
    (dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
      (AlgebraVertex (F.obj k))ᵒᵖ (diagramAlgebraVertexTransition F (h.trans g)).op)
    (diagramAlgebraDerivedRestrictionCompIso F h g)
  rw [diagramAlgebraDerivedExtensionComparison_adjunct,
    diagramAlgebraDerivedExtensionComparison_adjunct,
    diagramAlgebraDerivedExtensionComparison_adjunct]
  exact diagramAlgebraDerivedRestrictionComparison_comp F h g X

/-- 概要：恒等包含の指定導来係数拡大比較は可逆。
方針：標準単位自然同型の成分との一致を使う。
規約：KST §3.1。使われ方：cartesian 条件の恒等包含の確認。 -/
theorem diagramAlgebraDerivedExtensionComparison_id_isIso (i : J)
    (X : DerivedAllDiagramModules F) :
    IsIso (diagramAlgebraDerivedExtensionComparison F (le_refl i) X) := by
  rw [diagramAlgebraDerivedExtensionComparison_id]
  infer_instance

/-- 概要：指定導来係数拡大比較の自然変換の単位条件。
方針：証明済み対象ごとの単位条件を自然変換の成分で確認する。
規約：KST §3.1。使われ方：coherent な局所係数拡大図式の単位。 -/
theorem diagramAlgebraDerivedExtensionNatTrans_id (i : J) :
    diagramAlgebraDerivedExtensionNatTrans F (le_refl i) =
      whiskerLeft (diagramAlgebraDerivedEvaluation F i)
        (diagramAlgebraDerivedExtensionIdIso F i).hom := by
  apply NatTrans.ext
  funext X
  exact diagramAlgebraDerivedExtensionComparison_id F i X

/-- 概要：指定導来係数拡大比較の自然変換の合成条件。
方針：証明済み対象ごとの三重条件を自然変換の成分で確認する。
規約：KST §3.1。使われ方：coherent な cartesian 比較の三重等式。 -/
theorem diagramAlgebraDerivedExtensionNatTrans_comp {i j k : J} (h : i ≤ j) (g : j ≤ k) :
    whiskerRight (diagramAlgebraDerivedExtensionNatTrans F h) (diagramAlgebraDerivedExtension F g) ≫
        diagramAlgebraDerivedExtensionNatTrans F g =
      whiskerLeft (diagramAlgebraDerivedEvaluation F i)
        (diagramAlgebraDerivedExtensionCompIso F h g).hom ≫
      diagramAlgebraDerivedExtensionNatTrans F (h.trans g) := by
  apply NatTrans.ext
  funext X
  exact diagramAlgebraDerivedExtensionComparison_comp F h g X

end SerrePositivity.KST.DerivedBlowup
