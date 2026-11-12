module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation

/-!
概要：既存の相対 curry の指定同型の成分を元の比較の同じ係数への制限と同定する。
方針：元の豊穣作用・既存の成分評価・端点表示の三つの比較を合成する。
規約：元の指定同型を保持。使われ方：unstraightening 三角形比較の一点での値。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 既存の指定 curry 同型の成分は、元の指定比較を同じ係数で制限したもの。 -/
lemma relativeFunctorCurryIso_app {A E B L : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) [Quasicategory L] [Quasicategory (relativeFunctorSpace p a)]
    (H H' : A ⊗ L ⟶ E)
    (hH : H ≫ p = fst A L ≫ a) (hH' : H' ≫ p = fst A L ≫ a)
    (e : VertexIso (relativeFunctorVertex p (fst A L ≫ a) H hH)
      (relativeFunctorVertex p (fst A L ≫ a) H' hH')) (l : L _⦋0⦌) :
    HEq ((relativeFunctorCurryIso p a H H' hH hH' e).app l)
      (VertexIso.map e
        (relativeFunctorPre p (fst A L ≫ a) (lift (𝟙 A) (SSet.const l)))) := by
  have hm := vertexIso_map_heq_of_heq
    (VertexIso.map e (relativeFunctorCurryHom p a L))
    (relativeFunctorCurryIso p a H H' hH hH' e)
    (relativeFunctorCurryHom_vertex p a H hH)
    (relativeFunctorCurryHom_vertex p a H' hH')
    (relativeFunctorCurryIso_heq_map p a H H' hH hH' e).symm (evaluateFunctorAt l)
  exact (functorIso_app_heq_evaluate (relativeFunctorCurryIso p a H H' hH hH' e) l).trans
    (hm.symm.trans (relativeFunctorCurryHom_vertexIso_evaluate p a L l e))

end SerrePositivity.InfinityCategories.F2
