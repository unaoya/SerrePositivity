module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientLocalSquares
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedEvaluation
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionCoherence

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の係数表示変更と指定局所評価の比較。
方針：指定局所埋め込みの可換四角形を、加群制限・導来制限の標準合成同型へ移す。
規約：任意の全図式加群に自然な比較。cartesian 条件の保存は別に検証する。
使われ方：係数図式同型の導来比較を局所 perfect 条件へ制限する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable {F G : J ⥤ Mon (Complex R)} (α : F ⟶ G)
variable [Small.{u} (DiagramModuleCoefficientObject F)]
variable [Small.{u} (DiagramModuleCoefficientObject G)]

/-- 概要：任意の係数図式射に沿う全図式加群の指定制限。
方針：指定係数 dg 関手の opposite の opposite に沿う加群制限を使う。
規約：KST §3.1。使われ方：局所評価比較の始点。 -/
abbrev diagramCoefficientRestriction :=
  moduleRestriction R (DiagramModuleCoefficientObject F)ᵒᵖ
    (DiagramModuleCoefficientObject G)ᵒᵖ (diagramCoefficientDGFunctor α).op.op

/-- 概要：任意の係数図式射に沿う全図式加群の指定導来制限。
方針：構成済み係数 dg 関手の opposite に沿う既存導来制限を使う。
規約：KST §3.1。使われ方：全対象の局所条件の表示比較。 -/
abbrev diagramCoefficientDerivedRestrictionOf :=
  dgDerivedRestriction R (DiagramModuleCoefficientObject F)ᵒᵖ
    (DiagramModuleCoefficientObject G)ᵒᵖ (diagramCoefficientDGFunctor α).op

/-- 概要：局所係数代数の指定成分に沿う導来制限。
方針：成分を一対象 dg 関手に送り、既存導来制限を適用する。
規約：KST Lemma 3.6。使われ方：表示変更後の局所評価の比較先。 -/
abbrev diagramCoefficientLocalDerivedRestriction (i : J) :=
  dgDerivedRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (G.obj i))ᵒᵖ
    (algebraVertexMap (α.app i)).op

/-- 概要：係数制限後の指定加群局所評価と局所成分に沿う制限の自然同型。
方針：指定局所埋め込みの可換式に二つの標準制限合成同型を適用する。
規約：KST §3.1、同じ局所 dg 関手に二経路をまとめる指定比較。
使われ方：主局所化前の局所表示比較。 -/
def diagramCoefficientModuleEvaluationIso (i : J) :
    diagramCoefficientRestriction α ⋙ diagramAlgebraModuleEvaluation F i ≅
      diagramAlgebraModuleEvaluation G i ⋙
        moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (G.obj i))ᵒᵖ
          (algebraVertexMap (α.app i)).op.op :=
  transitionRestrictionCompIso (diagramAlgebraVertexEmbedding F i)
    (diagramCoefficientDGFunctor α)
    ((diagramAlgebraVertexEmbedding F i).comp (diagramCoefficientDGFunctor α)) rfl ≪≫
  (transitionRestrictionCompIso (algebraVertexMap (α.app i)) (diagramAlgebraVertexEmbedding G i)
    ((diagramAlgebraVertexEmbedding F i).comp (diagramCoefficientDGFunctor α))
    (diagramCoefficientDGFunctor_vertex α i).symm).symm

/-- 概要：係数導来制限後の指定局所評価と局所導来制限の自然同型。
方針：局所化前の標準合成比較を延長した二つの指定導来合成同型を使う。
規約：KST §3.1・Lemma 3.6、全導来対象で自然。
使われ方：局所 perfect 性と canonical な cartesian 比較の表示変更。 -/
def diagramCoefficientDerivedEvaluationIso (i : J) :
    diagramCoefficientDerivedRestrictionOf α ⋙ diagramAlgebraDerivedEvaluation F i ≅
      diagramAlgebraDerivedEvaluation G i ⋙ diagramCoefficientLocalDerivedRestriction α i :=
  transitionDerivedRestrictionCompIso (diagramAlgebraVertexEmbedding F i)
    (diagramCoefficientDGFunctor α)
    ((diagramAlgebraVertexEmbedding F i).comp (diagramCoefficientDGFunctor α)) rfl ≪≫
  (transitionDerivedRestrictionCompIso (algebraVertexMap (α.app i))
    (diagramAlgebraVertexEmbedding G i)
    ((diagramAlgebraVertexEmbedding F i).comp (diagramCoefficientDGFunctor α))
    (diagramCoefficientDGFunctor_vertex α i).symm).symm

end SerrePositivity.KST.DerivedBlowup
