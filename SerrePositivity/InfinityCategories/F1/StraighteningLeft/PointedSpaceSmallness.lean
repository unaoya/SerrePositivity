module

public import SerrePositivity.InfinityCategories.F1.Coherent.RestrictionsSmallness
public import SerrePositivity.InfinityCategories.F1.Joins.JoinSmallness

/-!
概要：普遍的な pointed-space 射影の固定した単体上の小ささ。
方針：coslice の単体を join からの写像に戻し、左右の制限で全頂点の対象を固定する。
規約：元の coslice は宇宙 u+1 のまま、各次数の集合の小ささを宇宙 u で示す。
使われ方：Kerodon §5.5.2、Corollary 5.6.0.6、一般の coherent な図式の小さい unstraightening。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：普遍的な pointed-space 射影の指定単体上の逆像は u に小さい。
方針：join の左右の制限を固定した写像の型へ単射で写し、coherent な制限の小ささを使う。
規約：次数 n と底の単体 s は任意。
使われ方：Kerodon Proposition 5.5.2.2、Corollary 5.6.0.6、unstraightening の各次数の宇宙縮小。 -/
lemma pointedSpaceProjection_simplexFiber_small (n : SimplexCategoryᵒᵖ)
    (s : SpaceInfinity.{u}.obj n) :
    Small.{u} {t : PointedSpaceInfinity.{u}.obj n // pointedSpaceProjection.app n t = s} := by
  let K : SSet.{u + 1} := Δ[0]
  let L : SSet.{u + 1} := stdSimplex.obj n.unop
  have (k : SimplexCategoryᵒᵖ) : Small.{u} (K.obj k) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (k.unop ⟶ ⦋0⦌)))
  have (k : SimplexCategoryᵒᵖ) : Small.{u} (L.obj k) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (k.unop ⟶ n.unop)))
  have hsmall := coherentMap_fixedRestrictions_small.{u, u + 1} (D := KanObject.{u})
    (joinInl K L) (joinInr K L) (SSet.yonedaEquiv.symm pointSpaceVertex.{u})
    (SSet.yonedaEquiv.symm s) (join_vertices_covered K L)
  let T := {f : join K L ⟶ SpaceInfinity.{u} //
    joinInl K L ≫ f = SSet.yonedaEquiv.symm pointSpaceVertex.{u} ∧
      joinInr K L ≫ f = SSet.yonedaEquiv.symm s}
  have : Small.{u} T := hsmall
  let code : {t : PointedSpaceInfinity.{u}.obj n // pointedSpaceProjection.app n t = s} → T :=
    fun t ↦ ⟨t.val.val, t.val.property, by
      apply SSet.yonedaEquiv.injective
      simp only [Equiv.apply_symm_apply]
      have ht := t.property
      change SSet.yonedaEquiv (joinInr K L ≫ t.val.val) = s at ht
      exact ht⟩
  apply small_of_injective (f := code)
  intro t t' h
  apply Subtype.ext
  apply Subtype.ext
  change (code t).val = (code t').val
  exact congrArg Subtype.val h

end SerrePositivity.InfinityCategories
