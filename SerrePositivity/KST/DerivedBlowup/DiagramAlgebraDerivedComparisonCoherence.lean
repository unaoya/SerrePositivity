module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComputation
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedRestrictionCoherence
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraModuleComparisonCoherence

/-!
概要：KST §3.1 の正規表示における指定導来制限比較の単位・三重整合性。
方針：主局所化の自然変換の単射性で実加群上へ戻し、既存の加群比較の等式を送る。
規約：標準導来制限単位・合成同型を介する指定経路の等式。
使われ方：導来係数拡大の随伴比較へ整合性を移す。
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

set_option maxHeartbeats 2000000 in
-- 主局所化上の自然変換を実加群の比較の局所化へ照合するために必要。
/-- 概要：指定導来制限比較の恒等包含に沿う合成は恒等自然変換。
方針：局所化前の対象で四成分を計算し、加群比較の単位条件を送る。
規約：KST §3.1。使われ方：導来局所比較の単位条件。 -/
theorem diagramAlgebraDerivedRestrictionNatTrans_id (i : J) :
    diagramAlgebraDerivedRestrictionNatTrans F (le_refl i) ≫
      whiskerLeft (diagramAlgebraDerivedEvaluation F i)
        (diagramAlgebraDerivedRestrictionIdIso F i).hom =
      𝟙 (diagramAlgebraDerivedEvaluation F i) := by
  apply moduleDerivedNatTrans_ext R (DiagramModuleCoefficientObject F)ᵒᵖ
  intro M
  change (diagramAlgebraDerivedRestrictionNatTrans F (le_refl i)).app
      ((moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj M) ≫
      (diagramAlgebraDerivedRestrictionIdIso F i).hom.app
        ((moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).obj
          ((diagramAlgebraModuleEvaluation F i).obj M)) = 𝟙 _
  rw [diagramAlgebraDerivedRestrictionNatTrans_app_Q_map F (le_refl i) M,
    diagramAlgebraDerivedRestrictionIdIso_hom_app_Q]
  change (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
      (diagramAlgebraModuleComparison F (le_refl i) M) ≫
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
        ((diagramAlgebraRestrictionIdIso F i).hom.app
          ((diagramAlgebraModuleEvaluation F i).obj M)) =
    𝟙 ((moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).obj
      ((diagramAlgebraModuleEvaluation F i).obj M))
  simpa only [Functor.map_comp, CategoryTheory.Functor.map_id, Functor.id_obj] using
    congrArg (fun f => (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map f)
      (diagramAlgebraModuleComparison_id F i M)

set_option maxHeartbeats 2000000 in
-- 三つの導来評価と標準制限合成同型の計算経路を照合するために必要。
/-- 概要：二段の指定導来制限比較は標準合成同型を介して直接比較に一致する。
方針：局所化前の各対象で計算し、加群比較の三重整合性の局所化像を使う。
規約：KST §3.1。使われ方：指定導来局所比較の三重条件。 -/
theorem diagramAlgebraDerivedRestrictionNatTrans_comp {i j k : J} (h : i ≤ j) (g : j ≤ k) :
    diagramAlgebraDerivedRestrictionNatTrans F h ≫
      whiskerRight (diagramAlgebraDerivedRestrictionNatTrans F g)
        (diagramAlgebraDerivedRestriction F h) ≫
      whiskerLeft (diagramAlgebraDerivedEvaluation F k)
        (diagramAlgebraDerivedRestrictionCompIso F h g).hom =
      diagramAlgebraDerivedRestrictionNatTrans F (h.trans g) := by
  apply moduleDerivedNatTrans_ext R (DiagramModuleCoefficientObject F)ᵒᵖ
  intro M
  change (diagramAlgebraDerivedRestrictionNatTrans F h).app
      ((moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj M) ≫
      (diagramAlgebraDerivedRestriction F h).map
        ((diagramAlgebraDerivedRestrictionNatTrans F g).app
          ((moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj M)) ≫
      (diagramAlgebraDerivedRestrictionCompIso F h g).hom.app
        ((moduleToDerived R (AlgebraVertex (F.obj k))ᵒᵖ).obj
          ((diagramAlgebraModuleEvaluation F k).obj M)) =
    (diagramAlgebraDerivedRestrictionNatTrans F (h.trans g)).app
      ((moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj M)
  rw [diagramAlgebraDerivedRestrictionNatTrans_app_Q_map F h M,
    diagramAlgebraDerivedRestrictionNatTrans_app_Q_map F g M,
    diagramAlgebraDerivedRestrictionNatTrans_app_Q_map F (h.trans g) M,
    transitionDerivedRestriction_map_Q (diagramAlgebraVertexTransition F h),
    diagramAlgebraDerivedRestrictionCompIso_hom_app_Q]
  simpa only [Functor.map_comp] using
    congrArg (fun f => (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map f)
      (diagramAlgebraModuleComparison_comp F h g M)

/-- 概要：指定導来制限比較の各対象での単位条件。
方針：自然変換の単位等式を当該対象で評価する。
規約：KST §3.1。使われ方：導来係数拡大比較の随伴での単位計算。 -/
theorem diagramAlgebraDerivedRestrictionComparison_id (i : J) (X : DerivedAllDiagramModules F) :
    (diagramAlgebraDerivedRestrictionNatTrans F (le_refl i)).app X ≫
      (diagramAlgebraDerivedRestrictionIdIso F i).hom.app
        ((diagramAlgebraDerivedEvaluation F i).obj X) = 𝟙 _ :=
  congrArg (fun τ => τ.app X) (diagramAlgebraDerivedRestrictionNatTrans_id F i)

/-- 概要：指定導来制限比較の各対象での三重条件。
方針：自然変換の合成等式を当該対象で評価する。
規約：KST §3.1。使われ方：導来係数拡大比較の随伴での三重計算。 -/
theorem diagramAlgebraDerivedRestrictionComparison_comp {i j k : J} (h : i ≤ j) (g : j ≤ k)
    (X : DerivedAllDiagramModules F) :
    (diagramAlgebraDerivedRestrictionNatTrans F h).app X ≫
      (diagramAlgebraDerivedRestriction F h).map
        ((diagramAlgebraDerivedRestrictionNatTrans F g).app X) ≫
      (diagramAlgebraDerivedRestrictionCompIso F h g).hom.app
        ((diagramAlgebraDerivedEvaluation F k).obj X) =
      (diagramAlgebraDerivedRestrictionNatTrans F (h.trans g)).app X :=
  congrArg (fun τ => τ.app X) (diagramAlgebraDerivedRestrictionNatTrans_comp F h g)

end SerrePositivity.KST.DerivedBlowup
