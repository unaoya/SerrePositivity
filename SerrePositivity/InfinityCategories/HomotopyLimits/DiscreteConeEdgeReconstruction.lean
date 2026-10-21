module

public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteConeFromEdges

/-!
概要：元の離散図式上の全錐は、元の頂点と全脚の全一単体から厳密に再構成できる。
方針：元の錐を頂点下の coslice に curry し、全離散頂点で比較する。
規約：充填性・有限性は不要。元の全錐を等式で回収する。
使われ方：評価した元の有限錐を Kan 射の通常の錐と照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の native 脚を表す区間の射は、元の標準脚包含の前合成そのもの。 -/
lemma nativeConeLeg_arrow {K X : SSet.{u + 1}} {p : K ⟶ X} (c : JoinCone p)
    (k : K _⦋0⦌) : SSet.yonedaEquiv.symm (F2.nativeConeLeg c k).edge =
      F2.coneLegInclusion k ≫ c.val := by
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (F2.coneLegInclusion k ≫ c.val)) = _
  exact SSet.yonedaEquiv.symm_apply_apply _

/-- 元の全錐を元の頂点と全脚の全一単体から再構成すると、元の全錐そのもの。 -/
lemma discreteConeFromEdges_eta {J : Type u} {X : SSet.{u + 1}}
    {p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶ X}
    (c : JoinCone p) :
    discreteConeFromEdges p (fun j ↦ F2.nativeConeLeg c
      (ULift.up (nerveVertex (Discrete.mk j)))) = c := by
  have hfix : joinInl _ _ ≫ c.val = SSet.yonedaEquiv.symm c.vertex :=
    (SSet.yonedaEquiv.symm_apply_apply (joinInl _ _ ≫ c.val)).symm
  let g := sliceUnderCurry c.val hfix
  have hg : g = discreteEdgeConeFamily p (fun j ↦ F2.nativeConeLeg c
      (ULift.up (nerveVertex (Discrete.mk j)))) := by
    apply liftedDiscreteDiagram_ext
    intro j
    rw [discreteEdgeConeFamily_vertex]
    apply Subtype.ext
    change joinMap (𝟙 _) (SSet.yonedaEquiv.symm (ULift.up (nerveVertex j))) ≫ c.val =
      (joinStdSimplexIso 0 0).hom ≫
        SSet.yonedaEquiv.symm (F2.nativeConeLeg c (ULift.up (nerveVertex j))).edge
    erw [nativeConeLeg_arrow, F2.coneLegInclusion, ← Category.assoc, Iso.hom_inv_id_assoc]
  apply Subtype.ext
  change sliceUnderUncurry (discreteEdgeConeFamily p _) = c.val
  rw [← hg, sliceUnderUncurry_curry]

/-- 元の離散図式の全錐は、元の頂点と全脚の全一単体だけで一意に決まる。 -/
lemma discreteCone_ext_of_vertex_leg {J : Type u} {X : SSet.{u + 1}}
    {p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶ X}
    (c d : JoinCone p) (hv : c.vertex = d.vertex)
    (he : ∀ j : J, (F2.nativeConeLeg c (ULift.up (nerveVertex (Discrete.mk j)))).edge =
      (F2.nativeConeLeg d (ULift.up (nerveVertex (Discrete.mk j)))).edge) : c = d := by
  have hc : joinInl _ _ ≫ c.val = SSet.yonedaEquiv.symm d.vertex :=
    (SSet.yonedaEquiv.symm_apply_apply (joinInl _ _ ≫ c.val)).symm.trans
      (congrArg SSet.yonedaEquiv.symm hv)
  have hd : joinInl _ _ ≫ d.val = SSet.yonedaEquiv.symm d.vertex :=
    (SSet.yonedaEquiv.symm_apply_apply (joinInl _ _ ≫ d.val)).symm
  have h : sliceUnderCurry c.val hc = sliceUnderCurry d.val hd := by
    apply liftedDiscreteDiagram_ext
    intro j
    apply Subtype.ext
    change joinMap (𝟙 _) (SSet.yonedaEquiv.symm (ULift.up (nerveVertex j))) ≫ c.val =
      joinMap (𝟙 _) (SSet.yonedaEquiv.symm (ULift.up (nerveVertex j))) ≫ d.val
    apply (cancel_epi (joinStdSimplexIso 0 0).inv).mp
    change F2.coneLegInclusion _ ≫ c.val = F2.coneLegInclusion _ ≫ d.val
    rw [← nativeConeLeg_arrow, ← nativeConeLeg_arrow, he j.as]
  apply Subtype.ext
  exact (sliceUnderUncurry_curry c.val hc).symm.trans
    ((congrArg sliceUnderUncurry h).trans (sliceUnderUncurry_curry d.val hd))

end SerrePositivity.InfinityCategories.HomotopyLimits
