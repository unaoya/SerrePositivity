module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PrecompositionIdentityEvaluation

/-!
概要：元の Hom の転置を一点で評価して元の二胞体の成分へ戻す。
方針：交換と評価の厳密な可換性を h に写し、端点の輸送を相殺する。
規約：元の二胞体と指定された頂点を保持する。
使われ方：前合成の随伴単位の恒等関手での成分の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：転置した関手を指定点で評価した関手頂点は元の族の同じ点での値。
方針：交換と評価の可換性を零次の成分で読む。
規約：充填性の仮定は不要。
使われ方：転置した Hom の評価の両端の正規化。 -/
lemma transposeEvaluation_vertex {A B Z : SSet.{u}}
    (U : A ⟶ (ihom B).obj Z) (x : A _⦋0⦌) :
    functorVertex (F1B.functorTranspose U ≫ evaluateFunctorAt (Y := Z) x) =
      U.app (Opposite.op ⦋0⦌) x := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (internalHomSwapIso_evaluate A B Z x) (Opposite.op ⦋0⦌)) (functorVertex U)
  change functorVertex (F1B.functorTranspose U ≫ evaluateFunctorAt (Y := Z) x) =
    (evaluateFunctorAt (Y := (ihom B).obj Z) x).app (Opposite.op ⦋0⦌) (functorVertex U) at h
  exact h.trans (evaluateFunctorAt_functorVertex x U)

/-- 概要：転置した Hom の評価を端点の元の値へ輸送すると元の Hom の成分になる。
方針：交換・評価の可換性を h の射に適用し、端点輸送の連結を相殺する。
規約：全関手圏の任意の二胞体と指定点を保持する。
使われ方：前合成の単位成分の回収。 -/
lemma transposeHomEquiv_evaluate {A B Z : SSet.{u}} [Quasicategory Z]
    {U V : A ⟶ (ihom B).obj Z} (α : FunctorHom U V) (x : A _⦋0⦌) :
    eqToHom (congrArg HomotopyCategory.mk (transposeEvaluation_vertex U x)).symm ≫
      (hoFunctor.map ((ihom B).map (evaluateFunctorAt (Y := Z) x))).toFunctor.map
        (transposeHomEquiv U V α) ≫
      eqToHom (congrArg HomotopyCategory.mk (transposeEvaluation_vertex V x)) =
      functorHomEvaluate α x := by
  change eqToHom (congrArg HomotopyCategory.mk (transposeEvaluation_vertex U x)).symm ≫
    (hoFunctor.map ((ihom B).map (evaluateFunctorAt (Y := Z) x))).toFunctor.map
      ((hoFunctor.map (internalHomSwapIso A B Z).hom).toFunctor.map α) ≫
    eqToHom (congrArg HomotopyCategory.mk (transposeEvaluation_vertex V x)) = _
  have h := CategoryTheory.Functor.congr_hom
    (congrArg (fun f ↦ (hoFunctor.map f).toFunctor) (internalHomSwapIso_evaluate A B Z x)) α
  rw [hoFunctor_map_comp_apply] at h
  rw [h]
  simp only [functorHomEvaluate, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
