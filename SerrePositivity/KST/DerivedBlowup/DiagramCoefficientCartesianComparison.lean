module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientAdjunctSquare
public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientLocallyPerfect
public import SerrePositivity.KST.DerivedBlowup.AdjointSquareComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraCartesianCondition

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の係数図式同型と cartesian 比較。
方針：指定制限比較の可換四角形を随伴へ移し、局所 Morita 同値の余単位を消去する。
規約：canonical な係数拡大比較の可逆性を比較する。
使われ方：例外因子の共通 Koszul 表示で大域 Perf 候補を扱う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
namespace SerrePositivity.KST.DerivedBlowup
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable {F G : J ⥤ Mon (Complex R)}
variable [Small.{u} (DiagramModuleCoefficientObject F)]
variable [Small.{u} (DiagramModuleCoefficientObject G)]

set_option maxHeartbeats 4000000 in
-- 四つの graph 随伴と指定局所評価同型の対象を照合するために必要。
/-- 概要：係数図式同型で canonical な局所係数拡大比較の可逆性は一致する。
方針：指定制限の可換式と局所同値の余単位を随伴四角形へ適用する。
規約：KST §3.1・Lemma 3.6、係数図式模型での再構成。
使われ方：全包含での cartesian 条件の保存・反映。 -/
theorem diagramCoefficientDerivedExtensionComparison_isIso_iff (e : F ≅ G)
    {i j : J} (h : i ≤ j) (X : DerivedAllDiagramModules G) :
    IsIso (diagramAlgebraDerivedExtensionComparison G h X) ↔
      IsIso (diagramAlgebraDerivedExtensionComparison F h
        ((diagramCoefficientDerivedRestrictionOf e.hom).obj X)) := by
  let Γᵢ := (algebraVertexMap (e.hom.app i)).op
  let Γⱼ := (algebraVertexMap (e.hom.app j)).op
  have hΓᵢ := quasiEquivalence_op _ (algebraVertexMap_quasiEquivalence (e.app i))
  have hΓⱼ := quasiEquivalence_op _ (algebraVertexMap_quasiEquivalence (e.app j))
  let Aᵢ := dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
    (AlgebraVertex (G.obj i))ᵒᵖ Γᵢ
  let Aⱼ := dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj j))ᵒᵖ
    (AlgebraVertex (G.obj j))ᵒᵖ Γⱼ
  let : IsIso (Aᵢ.counit.app ((diagramAlgebraDerivedEvaluation G i).obj X)) :=
    dgDerivedExtensionCounit_isIso_all R _ _ Γᵢ hΓᵢ _
  let : IsIso (Aⱼ.counit.app ((diagramAlgebraDerivedEvaluation G j).obj X)) :=
    dgDerivedExtensionCounit_isIso_all R _ _ Γⱼ hΓⱼ _
  let : (dgDerivedExtension R (AlgebraVertex (F.obj j))ᵒᵖ
      (AlgebraVertex (G.obj j))ᵒᵖ Γⱼ).IsEquivalence :=
    (dgFunctorDerivedEquivalence R _ _ Γⱼ hΓⱼ).isEquivalence_functor
  let g := (diagramAlgebraDerivedExtension F h).map
      ((diagramCoefficientDerivedEvaluationIso e.hom i).inv.app X) ≫
    diagramAlgebraDerivedExtensionComparison F h
      ((diagramCoefficientDerivedRestrictionOf e.hom).obj X) ≫
    (diagramCoefficientDerivedEvaluationIso e.hom j).hom.app X
  have he : IsIso (diagramAlgebraDerivedExtensionComparison G h X) ↔ IsIso g := by
    apply adjointSquare_comparison_isIso_iff Aᵢ Aⱼ
      (dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (G.obj i))ᵒᵖ
        (AlgebraVertex (G.obj j))ᵒᵖ (diagramAlgebraVertexTransition G h).op)
      (dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
        (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op)
      (diagramCoefficientDerivedTransitionIso e.hom h).symm
      (diagramAlgebraDerivedExtensionComparison G h X) g
    rw [diagramAlgebraDerivedExtensionComparison_adjunct]
    exact diagramCoefficientDerivedComparison_adjunct e.hom h X
  rw [he]
  dsimp only [g]
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

/-- 概要：係数図式同型の導来制限は cartesian 条件を保存・反映する。
方針：全包含の指定係数拡大比較の可逆性の iff を適用する。
規約：KST §3.1。使われ方：大域 Perf 候補への表示同値の制限。 -/
theorem diagramCoefficientDerivedRestriction_cartesian_iff (e : F ≅ G)
    (X : DerivedAllDiagramModules G) :
    diagramAlgebraCartesian F ((diagramCoefficientDerivedRestriction e).obj X) ↔
      diagramAlgebraCartesian G X := by
  constructor
  · intro hc i j h
    exact (diagramCoefficientDerivedExtensionComparison_isIso_iff e h X).mpr (hc i j h)
  · intro hc i j h
    exact (diagramCoefficientDerivedExtensionComparison_isIso_iff e h X).mp (hc i j h)

end SerrePositivity.KST.DerivedBlowup
