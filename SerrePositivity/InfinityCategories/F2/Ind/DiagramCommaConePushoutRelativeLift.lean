module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaCoconeLiftComp
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaConePushoutExtension

/-!
概要：極大点を余錐形状で追加しても、既存部分の指定部分形状への厳密持ち上げを保つ。
方針：既存部分で指定余錐を持ち上げ、その全余錐を保つ点追加拡張と接続する。
規約：元の全試験族と固定部分の指定余錐を保持する。
使われ方：下方閉部分を固定する有限半順序の極大点除去帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：既存部分の内部にある固定部分への厳密な余錐持ち上げは点追加で保たれる。
方針：二段制限の持ち上げと余錐 pushout 拡張。
規約：同じ固定全余錐。使われ方：下方部分固定帰納の段階。 -/
lemma exists_diagramComma_cocone_cone_pushout_fix_subshape
    (κ : Cardinal.{u}) [Fact κ.IsRegular] {U L K₁ K C A : SSet.{u}} [Quasicategory C]
    {i : L ⟶ K₁} {r : K₁ ⟶ K} {s : join L (Δ[0] : SSet.{u}) ⟶ K}
    (h : IsPushout i (joinInl L (Δ[0] : SSet.{u})) r s)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C) (t : U ⟶ K₁)
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D)
    (hLift : ∀ G : JoinCocone ((q ≫ diagramCommaRestriction κ D r) ≫
        diagramCommaRestriction κ ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D) t),
      ∃ c₁ : JoinCocone (q ≫ diagramCommaRestriction κ D r),
        mapJoinCocone
          (diagramCommaRestriction κ ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D) t) c₁ = G)
    (G : JoinCocone (q ≫ diagramCommaRestriction κ D (t ≫ r))) :
    ∃ c : JoinCocone q,
      mapJoinCocone (diagramCommaRestriction κ D (t ≫ r)) c = G := by
  exact exists_diagramComma_cocone_lift_comp κ D r t q
    (fun c₁ ↦ exists_diagramComma_cocone_cone_pushout κ h D hA hL q c₁) hLift G

end SerrePositivity.InfinityCategories.F2.Ind
