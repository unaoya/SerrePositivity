module

public import SerrePositivity.InfinityCategories.F1.Coherent.KanRightCompositionTransport
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluationVertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan

/-!
概要：一点からの射を固定した Kan Hom の合成を、元の点での評価に同定する。
方針：内部 Hom の前合成として表示し、一点評価の厳密な逆同型を使う。
規約：全 Hom パラメーターを保つ等式。
使われ方：右 Hom の合成輸送を元の Kan 空間の点評価へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 一点からの射を固定した豊穣合成は、同じ射による内部 Hom の前合成。 -/
lemma coherentKanPointComposition_pre (K L : KanObject.{u}) (f : pointKanObject ⟶ K) :
    lift (SSet.const (ULift.up (functorVertex f)))
      (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))) ≫
      coherentHomComposition pointKanObject K L =
        (SSet.uliftFunctor.{u + 1, u}).map
          ((pre (show (Δ[0] : SSet.{u}) ⟶ K.obj from f)).app L.obj) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  apply ULift.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 一点係数での豊穣合成は、元の点で評価した後に一点評価の逆同型を続ける射。 -/
lemma coherentKanPointComposition_evaluate (K L : KanObject.{u}) (z : K.obj _⦋0⦌) :
    lift (SSet.const (ULift.up (functorVertex (SSet.yonedaEquiv.symm z))))
      (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))) ≫
      coherentHomComposition pointKanObject K L =
        (SSet.uliftFunctor.{u + 1, u}).map
          (evaluateFunctorAt z ≫ (pointFunctorEvaluationIso L.obj).inv) := by
  rw [coherentKanPointComposition_pre]
  congr 1
  apply (cancel_mono (pointFunctorEvaluationIso L.obj).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (pre (SSet.yonedaEquiv.symm z)).app L.obj ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = _
  rw [evaluateFunctorAt_pre]
  congr 1
  have hp : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  rw [hp, SSet.yonedaEquiv_symm_app_id]

end SerrePositivity.InfinityCategories
