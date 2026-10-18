module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComparison

/-!
概要：KST §3.1 の正規表示の指定導来比較を実加群の主局所化上で計算する。
方針：局所化が対象を保持することから標準計算同型の成分を恒等へ簡約する。
規約：指定制限比較は元の加群比較の主局所化像と一致する。
使われ方：加群比較の単位・三重整合性を導来圏へ移す。
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

/-- 概要：正規表示の導来評価の標準計算同型の順成分は恒等。
方針：因子分解等式の対象成分は同一の局所化対象の等式となる。
規約：KST §3.1。使われ方：指定導来比較の計算で標準同型を消去する。 -/
theorem diagramAlgebraDerivedEvaluationIso_hom_app (i : J) (M : AllDiagramModules F) :
    (diagramAlgebraDerivedEvaluationIso F i).hom.app M = 𝟙 _ := by
  simp only [diagramAlgebraDerivedEvaluationIso, eqToIso.hom, eqToHom_app]
  rfl

/-- 概要：正規表示の導来評価の標準計算同型の逆成分は恒等。
方針：逆方向の対象等式も同一の局所化対象の等式となる。
規約：KST §3.1。使われ方：指定導来比較の始域を戻す計算。 -/
theorem diagramAlgebraDerivedEvaluationIso_inv_app (i : J) (M : AllDiagramModules F) :
    (diagramAlgebraDerivedEvaluationIso F i).inv.app M = 𝟙 _ := by
  simp only [diagramAlgebraDerivedEvaluationIso, eqToIso.inv, eqToHom_app]
  rfl

/-- 概要：反復制限の導来計算同型の順成分は恒等。
方針：評価の計算同型と局所制限の因子分解の対象成分を簡約する。
規約：KST §3.1。使われ方：導来比較の行先の計算。 -/
theorem diagramAlgebraDerivedRestrictedEvaluationIso_hom_app {i j : J} (h : i ≤ j)
    (M : AllDiagramModules F) :
    (diagramAlgebraDerivedRestrictedEvaluationIso F h).hom.app M = 𝟙 _ := by
  change (diagramAlgebraDerivedRestriction F h).map
      ((diagramAlgebraDerivedEvaluationIso F j).hom.app M) ≫
      (eqToIso (dgDerivedRestriction_fac R (AlgebraVertex (F.obj i))ᵒᵖ
        (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op)).hom.app
        ((diagramAlgebraModuleEvaluation F j).obj M) = _
  rw [diagramAlgebraDerivedEvaluationIso_hom_app, CategoryTheory.Functor.map_id]
  simp only [eqToIso.hom, eqToHom_refl, NatTrans.id_app, Functor.comp_obj, Category.id_comp]
  rfl

set_option maxHeartbeats 2000000 in
-- 反復評価の因子分解と主局所化上の Functor.map_id の型を照合するために必要。
/-- 概要：反復制限の導来計算同型の逆成分は恒等。
方針：局所制限の逆計算同型と評価の逆計算同型を簡約する。
規約：KST §3.1。使われ方：指定制限比較を加群比較の局所化へ戻す。 -/
theorem diagramAlgebraDerivedRestrictedEvaluationIso_inv_app {i j : J} (h : i ≤ j)
    (M : AllDiagramModules F) :
    (diagramAlgebraDerivedRestrictedEvaluationIso F h).inv.app M = 𝟙 _ := by
  change (eqToIso (dgDerivedRestriction_fac R (AlgebraVertex (F.obj i))ᵒᵖ
      (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op)).inv.app
      ((diagramAlgebraModuleEvaluation F j).obj M) ≫
      (diagramAlgebraDerivedRestriction F h).map
        ((diagramAlgebraDerivedEvaluationIso F j).inv.app M) = _
  rw [diagramAlgebraDerivedEvaluationIso_inv_app]
  dsimp only [Functor.comp]
  rw [CategoryTheory.Functor.map_id]
  simp only [eqToIso.inv, eqToHom_refl, NatTrans.id_app, Category.comp_id]
  rfl

/-- 概要：主局所化像における指定導来制限比較は延長前の指定成分。
方針：主局所化の自然変換延長の成分公式を使う。
規約：KST §3.1。使われ方：導来比較の等式を実加群で判定する。 -/
theorem diagramAlgebraDerivedRestrictionNatTrans_app_Q {i j : J} (h : i ≤ j)
    (M : AllDiagramModules F) :
    (diagramAlgebraDerivedRestrictionNatTrans F h).app
        ((moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj M) =
      (diagramAlgebraDerivedRestrictionPreNatTrans F h).app M :=
  Localization.Construction.NatTransExtension.app_eq _ M

/-- 概要：主局所化像における指定導来制限比較は指定加群比較の局所化像。
方針：前延長の三つの成分を展開し、標準計算同型の恒等成分を消去する。
規約：KST §3.1。使われ方：単位・三重整合性を主導来局所化へ送る。 -/
theorem diagramAlgebraDerivedRestrictionNatTrans_app_Q_map {i j : J} (h : i ≤ j)
    (M : AllDiagramModules F) :
    (diagramAlgebraDerivedRestrictionNatTrans F h).app
        ((moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj M) =
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
        (diagramAlgebraModuleComparison F h M) := by
  rw [diagramAlgebraDerivedRestrictionNatTrans_app_Q]
  change (diagramAlgebraDerivedEvaluationIso F i).hom.app M ≫
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
        (diagramAlgebraModuleComparison F h M) ≫
      (diagramAlgebraDerivedRestrictedEvaluationIso F h).inv.app M = _
  rw [diagramAlgebraDerivedEvaluationIso_hom_app,
    diagramAlgebraDerivedRestrictedEvaluationIso_inv_app]
  dsimp only [Functor.comp]
  simp only [Category.id_comp, Category.comp_id]

end SerrePositivity.KST.DerivedBlowup
