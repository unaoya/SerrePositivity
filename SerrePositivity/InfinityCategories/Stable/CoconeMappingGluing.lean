module
public import SerrePositivity.InfinityCategories.Stable.CoconeMappingSpace
public import SerrePositivity.InfinityCategories.Core.JoinPushout

/-! # 図式の pushout に沿う終点固定余錐の貼り合わせ

概要：両枝で共通部分に一致する終点固定の余錐は、一意に全図式へ貼り合わさる。
方針：coslice を uncurry し、join の pushout 保存で貼り合わせてから fiber 内へ戻す。
規約：パラメーターは任意の単体集合。使われ方：HA Lemma 1.1.2.10 の D(σ) の二枝表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：pushout 図式の両枝の整合する終点固定余錐を全図式へ延長できる。
方針：任意パラメーターとの join 後の pushout で uncurry した余錐を貼る。
規約：元の両枝と終点を厳密に保持。使われ方：余錐空間の pullback 表示の存在部分。 -/
lemma exists_coconeMappingSpace_glue {A B C D X T : SSet.{u}}
    {i : A ⟶ B} {j : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hP : IsPushout i j r s) (p : D ⟶ X) (y : X _⦋0⦌)
    (b : T ⟶ coconeMappingSpace (r ≫ p) y) (c : T ⟶ coconeMappingSpace (s ≫ p) y)
    (h : joinMap i (𝟙 T) ≫ sliceUnderUncurry (b ≫ vertexFiberι (sliceUnderProjection (r ≫ p)) y) =
      joinMap j (𝟙 T) ≫ sliceUnderUncurry (c ≫ vertexFiberι (sliceUnderProjection (s ≫ p)) y)) :
    ∃ a : T ⟶ coconeMappingSpace p y,
      a ≫ cosliceRestrictionFiberMap p r y = b ∧ a ≫ cosliceRestrictionFiberMap p s y = c := by
  let b' := b ≫ vertexFiberι (sliceUnderProjection (r ≫ p)) y
  let c' := c ≫ vertexFiberι (sliceUnderProjection (s ≫ p)) y
  let H := join_left_isPushout hP T
  let F := H.desc (sliceUnderUncurry b') (sliceUnderUncurry c') h
  have hf : joinInl D T ≫ F = p := by
    apply hP.hom_ext
    · calc
        _ = joinInl B T ≫ (joinMap r (𝟙 T) ≫ F) := by
          simp only [← Category.assoc, joinInl_joinMap]
        _ = _ := by rw [H.inl_desc, sliceUnderUncurry_fixed]
    · calc
        _ = joinInl C T ≫ (joinMap s (𝟙 T) ≫ F) := by
          simp only [← Category.assoc, joinInl_joinMap]
        _ = _ := by rw [H.inr_desc, sliceUnderUncurry_fixed]
  have hy : joinInr D T ≫ F = SSet.const y := by
    calc
      _ = joinInr B T ≫ (joinMap r (𝟙 T) ≫ F) := by
        simp only [← Category.assoc, joinInr_joinMap, Category.id_comp]
      _ = joinInr B T ≫ sliceUnderUncurry b' := by rw [H.inl_desc]
      _ = b' ≫ sliceUnderProjection (r ≫ p) := sliceUnderUncurry_projection b'
      _ = _ := by rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
  let q := sliceUnderCurry F hf
  have hq : q ≫ sliceUnderProjection p = SSet.const y := by
    rw [sliceUnderCurry_projection]
    exact hy
  let a := vertexFiberLift (sliceUnderProjection p) y q hq
  refine ⟨a, ?_, ?_⟩
  · apply vertexFiber_hom_ext
    rw [Category.assoc, coconeMappingSpace_restrict_ι, ← Category.assoc, vertexFiberLift_ι]
    apply sliceUnderUncurry_injective
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry]
    exact H.inl_desc _ _ _
  · apply vertexFiber_hom_ext
    rw [Category.assoc, coconeMappingSpace_restrict_ι, ← Category.assoc, vertexFiberLift_ι]
    apply sliceUnderUncurry_injective
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry]
    exact H.inr_desc _ _ _

/-- 概要：全図式の終点固定余錐の射は、pushout の二枝への制限で一意に定まる。
方針：fiber の包含と uncurry の単射性を使い、join 後の pushout の一意性に帰着する。
規約：パラメーターと値域の仮定は不要。使われ方：余錐空間の pullback 表示の一意性。 -/
lemma coconeMappingSpace_hom_ext_of_pushout {A B C D X T : SSet.{u}}
    {i : A ⟶ B} {j : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hP : IsPushout i j r s) (p : D ⟶ X) (y : X _⦋0⦌)
    {a b : T ⟶ coconeMappingSpace p y}
    (hr : a ≫ cosliceRestrictionFiberMap p r y = b ≫ cosliceRestrictionFiberMap p r y)
    (hs : a ≫ cosliceRestrictionFiberMap p s y = b ≫ cosliceRestrictionFiberMap p s y) : a = b := by
  apply vertexFiber_hom_ext
  apply sliceUnderUncurry_injective
  apply (join_left_isPushout hP T).hom_ext
  · have h := congrArg (fun f => f ≫ vertexFiberι (sliceUnderProjection (r ≫ p)) y) hr
    change (a ≫ vertexFiberι (sliceUnderProjection p) y) ≫ sliceUnderRestrict p r =
      (b ≫ vertexFiberι (sliceUnderProjection p) y) ≫ sliceUnderRestrict p r at h
    have he := congrArg sliceUnderUncurry h
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_restrict] at he
    exact he
  · have h := congrArg (fun f => f ≫ vertexFiberι (sliceUnderProjection (s ≫ p)) y) hs
    change (a ≫ vertexFiberι (sliceUnderProjection p) y) ≫ sliceUnderRestrict p s =
      (b ≫ vertexFiberι (sliceUnderProjection p) y) ≫ sliceUnderRestrict p s at h
    have he := congrArg sliceUnderUncurry h
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_restrict] at he
    exact he

end SerrePositivity.InfinityCategories
