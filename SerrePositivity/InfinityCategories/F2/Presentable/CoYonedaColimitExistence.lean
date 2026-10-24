module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoYonedaFullyFaithful
public import SerrePositivity.InfinityCategories.F2.Presentable.FullyFaithfulLimitCreation
public import SerrePositivity.InfinityCategories.Core.UniverseLimits

/-!
概要：元の全 Hom 図式の表現可能な極限から元の余極限の存在を回収する。
方針：充満忠実な co-Yoneda 像の極限を持ち上げ、宇宙変更と反転を戻す。
規約：表現可能性は全係数に自然な頂点同型で与える。
使われ方：Ind 延長と幾何学的実現による局所 Kan 余極限の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：全 co-Yoneda 図式の極限頂点が表現可能なら元の図式の余極限が存在する。
方針：同じ反対図式の持ち上げを充満忠実性で戻し、元の宇宙へ降ろす。
規約：元の任意の形状と全係数自然性を保持する。
使われ方：filtered・geometric な計算による重み付き余極限の存在。 -/
lemma hasColimit_of_coyoneda_limit_representable
    {K C : SSet.{u}} [Quasicategory C] (p : K ⟶ C)
    (c : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map p) ≫
      coyonedaInfinityMap C)) (hc : IsLimitCone c)
    (hrep : ∃ z : C _⦋0⦌, Nonempty (VertexIso
      (functorVertex (homInfinityCovariant z)) c.vertex)) : HasColimit p := by
  apply (F1B.kanHasColimit_iff_hasLimit_op p).mpr
  apply (hasLimit_iff_ulift (SSet.opFunctor.map p)).mpr
  apply hasLimit_of_fullyFaithful_image_limit_iso (coyonedaInfinityMap C)
    (coyonedaInfinityMap_isFullyFaithful C)
    ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map p)) c hc
  obtain ⟨z, ⟨e⟩⟩ := hrep
  exact ⟨ULift.up (SSet.opObjEquiv.symm z),
    ⟨eqToIso (congrArg HomotopyCategory.mk (coyonedaInfinityMap_vertex z)) ≪≫ e⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
