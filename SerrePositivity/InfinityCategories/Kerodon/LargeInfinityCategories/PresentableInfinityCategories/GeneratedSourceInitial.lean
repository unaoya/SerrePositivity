module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratedSourceEdges
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageIdentities

/-!
概要：固定始域の生成閉包内射の圏には、元の恒等射を表す実始対象がある。
方針：恒等射の脚の所属を直接検査し、周囲の coslice の始対象の境界充填を全部分圏へ戻す。
規約：終対象・局所置換・presentable 性はこの始対象からは主張しない。
使われ方：HTT 5.5.5.14 の固定始域圏の元の種と射の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

private lemma initialVertex_of_fullInclusion {X : SSet.{u + 1}} (P : X _⦋0⦌ → Prop)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u + 1}) _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x := by
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι
  intro n b hb
  have hbj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ (b ≫ j) = SSet.yonedaEquiv.symm x.val := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hx n (b ≫ j) hbj
  have hv : ∀ v, P (F.app (Opposite.op ⦋0⦌) v) := by
    intro v
    have hvb : v ∈ (boundary (n + 1)).obj (Opposite.op ⦋0⦌) := by
      have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n (stdSimplex.obj₀Equiv v)
      rwa [Equiv.symm_apply_apply] at h
    let w : (boundary (n + 1) : SSet.{u + 1}) _⦋0⦌ := ⟨v, hvb⟩
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app hF (Opposite.op ⦋0⦌)) w
    change F.app (Opposite.op ⦋0⦌) v = (b.app (Opposite.op ⦋0⦌) w).val at he
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (b.app _ w)
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P F hv
  refine ⟨L, ?_⟩
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι, hF]

/-- 元の恒等 coslice 点の実脚は、元の生成閉包に属する。 -/
lemma generatedSourceIdentity_leg_mem (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone x) (𝟙 Δ[0])).edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges := by
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.identityArrow_mem_generatedEdges edges x
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex] at hi
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] C).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] C) (SSet.const x))) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges at hi
  rw [Equiv.symm_apply_apply] at hi
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫ SSet.const x) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp, SSet.comp_const]
  exact hi

/-- 元の恒等射を、そのまま固定始域圏の頂点として保持する。 -/
def generatedSourceIdentity (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedSourceCategory edges x) _⦋0⦌ := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone x, ?_⟩
  intro α
  have ha : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  subst α
  have hid := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)).map_id (Opposite.op ⦋0⦌)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.leg (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)).map
    (𝟙 (Opposite.op ⦋0⦌))) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone x)) (𝟙 Δ[0])).edge ∈ _
  rw [hid]
  exact generatedSourceIdentity_leg_mem edges x

/-- 固定始域圏内の元の恒等射は、その圏の実始対象である。 -/
lemma generatedSourceIdentity_isInitial (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (generatedSourceIdentity edges x) :=
  initialVertex_of_fullInclusion _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_isInitialVertex x)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
