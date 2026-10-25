module

public import SerrePositivity.InfinityCategories.F2.Ind.IsoCoconeLift
public import SerrePositivity.InfinityCategories.F1.Simplicial.FullPosetSubsetNerveIso

/-!
概要：固定順序部分が全点を含む場合、元の全図式 comma の指定余錐は厳密に持ち上がる。
方針：元の部分型包含の nerve 写像の同型性を制限へ移す。
規約：同じ試験族と指定された全余錐を保持する。
使われ方：下方閉部分を固定する有限半順序帰納の基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：全ての点を含む部分型への制限で、元の指定余錐を厳密に持ち上げる。
方針：同型による持ち上げ。規約：元の包含。使われ方：下方部分固定帰納の基底。 -/
lemma exists_diagramComma_cocone_lift_full_posetSubset (κ : Cardinal.{u})
    {P : Type u} [PartialOrder P] (U : Set P) (hU : ∀ p, p ∈ U)
    {C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ IndInfinity κ C)
    {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D)
    (G : JoinCocone (q ≫ diagramCommaRestriction κ D
      (nerveMap (OrderHom.Subtype.val U).toFunctor))) :
    ∃ c : JoinCocone q, mapJoinCocone
      (diagramCommaRestriction κ D (nerveMap (OrderHom.Subtype.val U).toFunctor)) c = G := by
  letI := fullPosetSubsetNerveMap_isIso U hU
  exact exists_diagramComma_cocone_lift_of_shape_isIso κ D _ q G

end SerrePositivity.InfinityCategories.F2.Ind
