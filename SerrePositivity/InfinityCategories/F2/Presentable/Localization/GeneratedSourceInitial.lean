module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceEdges
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageIdentities

/-!
概要：固定始域の生成閉包内射の圏には、元の恒等射を表す実始対象がある。
方針：恒等射の脚の所属を直接検査し、周囲の coslice の始対象の境界充填を全部分圏へ戻す。
規約：終対象・局所置換・presentable 性はこの始対象からは主張しない。
使われ方：HTT 5.5.5.14 の固定始域圏の元の種と射の構成。
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
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

private lemma initialVertex_of_fullInclusion {X : SSet.{u + 1}} (P : X _⦋0⦌ → Prop)
    (x : (fullSubcomplexOnVertices X P : SSet.{u + 1}) _⦋0⦌) (hx : IsInitialVertex x.val) :
    IsInitialVertex x := by
  let j := (fullSubcomplexOnVertices X P).ι
  intro n b hb
  have hbj : boundaryVertex n 0 ≫ (b ≫ j) = SSet.yonedaEquiv.symm x.val := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hx n (b ≫ j) hbj
  have hv : ∀ v, P (F.app (Opposite.op ⦋0⦌) v) := by
    intro v
    have hvb : v ∈ (boundary (n + 1)).obj (Opposite.op ⦋0⦌) := by
      have h := vertex_mem_boundary n (stdSimplex.obj₀Equiv v)
      rwa [Equiv.symm_apply_apply] at h
    let w : (boundary (n + 1) : SSet.{u + 1}) _⦋0⦌ := ⟨v, hvb⟩
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app hF (Opposite.op ⦋0⦌)) w
    change F.app (Opposite.op ⦋0⦌) v = (b.app (Opposite.op ⦋0⦌) w).val at he
    rw [he]
    exact fullSubcomplexOnVertices_vertex (b.app _ w)
  let L := fullSubcomplexLift P F hv
  refine ⟨L, ?_⟩
  apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
  rw [Category.assoc, fullSubcomplexLift_ι, hF]

/-- 元の恒等 coslice 点の実脚は、元の生成閉包に属する。 -/
lemma generatedSourceIdentity_leg_mem (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    (JoinCocone.leg (cosliceIdentityCone x) (𝟙 Δ[0])).edge ∈ generatedEdges edges := by
  have hi := identityArrow_mem_generatedEdges edges x
  rw [constantFunctorMap_vertex] at hi
  change SSet.yonedaEquiv ((functorVertexEquiv Δ[1] C).symm
    ((functorVertexEquiv Δ[1] C) (SSet.const x))) ∈ generatedEdges edges at hi
  rw [Equiv.symm_apply_apply] at hi
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫ SSet.const x) ∈ generatedEdges edges
  rw [joinMap_id, Category.id_comp, SSet.comp_const]
  exact hi

/-- 元の恒等射を、そのまま固定始域圏の頂点として保持する。 -/
def generatedSourceIdentity (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    (generatedSourceCategory edges x) _⦋0⦌ := by
  refine ⟨cosliceIdentityCone x, ?_⟩
  intro α
  have ha : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  subst α
  have hid := (sliceUnder (SSet.yonedaEquiv.symm x)).map_id (Opposite.op ⦋0⦌)
  change (JoinCocone.leg (((sliceUnder (SSet.yonedaEquiv.symm x)).map
    (𝟙 (Opposite.op ⦋0⦌))) (cosliceIdentityCone x)) (𝟙 Δ[0])).edge ∈ _
  rw [hid]
  exact generatedSourceIdentity_leg_mem edges x

/-- 固定始域圏内の元の恒等射は、その圏の実始対象である。 -/
lemma generatedSourceIdentity_isInitial (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    IsInitialVertex (generatedSourceIdentity edges x) :=
  initialVertex_of_fullInclusion _ _ (cosliceIdentityCone_isInitialVertex x)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
