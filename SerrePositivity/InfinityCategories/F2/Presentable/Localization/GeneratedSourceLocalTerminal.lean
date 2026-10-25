module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceTerminalLocality
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedTargetIdentityTerminal
public import SerrePositivity.InfinityCategories.F2.Presentable.LocalSaturatedClosure

/-!
概要：固定始域の閉包内射は、その終域が局所的なら終対象となる。
方針：始点制限の自明 Kan 性から元の coslice の全写像空間を可縮にする。
規約：局所対象または終対象の存在は仮定から新たに作らない。
使われ方：HTT 5.5.5.14 の終対象と局所置換の特徴付け。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

private lemma sourceMapping_trivial_of_localObject
    {C : SSet.{u}} [Quasicategory C] {a b : C _⦋0⦌} (f : C.Edge a b)
    (W : Set (C _⦋1⦌)) (hf : f.edge ∈ W) (y : C _⦋0⦌) (hy : IsLocalObject W y) :
    TrivialKanFibration (edgeCosliceSourceMapping f y) := by
  have he : SSet.yonedaEquiv (SSet.yonedaEquiv.symm f.edge) ∈ W := by
    rw [Equiv.apply_symm_apply]
    exact hf
  have := sourceRestriction_trivial_of_localObject W (SSet.yonedaEquiv.symm f.edge) he hy
  change TrivialKanFibration (normalizedCoconeRestrictionFiber
    (SSet.yonedaEquiv.symm f.edge) (stdSimplex.δ (1 : Fin 2)) _ y)
  rw [normalizedCoconeRestrictionFiber_eq]
  exact ⟨trivialKanFibrations.comp_mem _ _
    TrivialKanFibration.mem (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 局所的な終域を持つ閉包内射は、同じ固定始域圏の終対象である。 -/
lemma generatedSource_isTerminal_of_target_isLocalObject
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌)
    (hs : IsLocalObject (Set.range edges) ((generatedSourceTarget edges x).app _ s)) :
    IsTerminalVertex s := by
  let y := (generatedSourceTarget edges x).app _ s
  have hy : IsLocalObject (generatedEdges edges) y :=
    (isLocalObject_stronglySaturatedClosure_iff (Set.range edges) hC y).mpr hs
  let g : (coconeMappingSpace (SSet.yonedaEquiv.symm x) y) _⦋0⦌ :=
    ⟨s.val, by rw [pinchedConstant_zero]; rfl⟩
  apply (generatedSource_isTerminal_iff_coslice_mapping_contractible edges x s).mpr
  intro t
  let f := SSet.Edge.ofTruncated (generatedSourceLeg edges x t)
  have := sourceMapping_trivial_of_localObject f (generatedEdges edges)
    (generatedSourceLeg_mem edges x t) y hy
  have hc := isContractibleKan_of_iso (edgeCosliceSourceMappingFiberIso f y g)
    (vertexFiber_isContractibleKan (edgeCosliceSourceMapping f y) g)
  have hr := (pinchedHomLeftRightEquivalence
    (edgeCosliceVertex f.toTruncated) g.val).isContractibleKan_iff.mp hc
  change IsContractibleKan (pinchedHom
    (edgeCosliceVertex (generatedSourceLeg edges x t)) s.val) at hr
  rw [edgeCosliceVertex_generatedSourceLeg] at hr
  exact hr

/-- 終対象性と元の生成族に対する終域の局所性は、存在する各射について同値。 -/
lemma generatedSource_isTerminal_iff_target_isLocalObject
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) :
    IsTerminalVertex s ↔
      IsLocalObject (Set.range edges) ((generatedSourceTarget edges x).app _ s) :=
  ⟨generatedSource_terminal_target_isLocalObject hC edges x s,
    generatedSource_isTerminal_of_target_isLocalObject hC edges x s⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
