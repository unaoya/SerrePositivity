module
public import SerrePositivity.InfinityCategories.Core.JoinPushout
public import SerrePositivity.InfinityCategories.F1.CosliceTriangleFiber

/-! # 図式の pushout に沿う可変終点の coslice 族の貼り合わせ

概要：図式の二枝上で整合する coslice の族は、終点を変えながら全図式へ一意に貼り合わさる。
方針：族を uncurry して任意パラメーターとの join 後の pushout を使う。
規約：終点を固定した fiber には限定しない。使われ方：二枝の終点輸送の区間族を貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：pushout の両枝上の整合する可変終点の余錐族は全図式に延長できる。
方針：uncurry した余錐を join 後の pushout で貼り、固定図式の条件を二枝で確認する。
規約：族の射影は左枝の射影を厳密に保つ。使われ方：余錐の終点輸送の区間族の構成。 -/
lemma exists_coslice_glue_of_pushout {A B C D X T : SSet.{u}}
    {i : A ⟶ B} {j : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hP : IsPushout i j r s) (p : D ⟶ X)
    (b : T ⟶ sliceUnder (r ≫ p)) (c : T ⟶ sliceUnder (s ≫ p))
    (h : joinMap i (𝟙 T) ≫ sliceUnderUncurry b =
      joinMap j (𝟙 T) ≫ sliceUnderUncurry c) :
    ∃ a : T ⟶ sliceUnder p,
      a ≫ sliceUnderRestrict p r = b ∧ a ≫ sliceUnderRestrict p s = c ∧
      a ≫ sliceUnderProjection p = b ≫ sliceUnderProjection (r ≫ p) := by
  let H := join_left_isPushout hP T
  let F := H.desc (sliceUnderUncurry b) (sliceUnderUncurry c) h
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
  let a := sliceUnderCurry F hf
  have hr : a ≫ sliceUnderRestrict p r = b := by
    apply sliceUnderUncurry_injective
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry]
    exact H.inl_desc _ _ _
  have hs : a ≫ sliceUnderRestrict p s = c := by
    apply sliceUnderUncurry_injective
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry]
    exact H.inr_desc _ _ _
  refine ⟨a, hr, hs, ?_⟩
  calc
    _ = a ≫ sliceUnderRestrict p r ≫ sliceUnderProjection (r ≫ p) :=
      congrArg (fun k => a ≫ k) (sliceUnderRestrict_projection p r).symm
    _ = _ := by rw [← Category.assoc, hr]

/-- 概要：全図式の可変終点の coslice 族は pushout の両枝への制限で決まる。
方針：uncurry 後の二枝を比較し、join 後の pushout の一意性を使う。
規約：値域やパラメーターの充填性は不要。使われ方：貼った輸送の両端を指定する。 -/
lemma coslice_hom_ext_of_pushout {A B C D X T : SSet.{u}}
    {i : A ⟶ B} {j : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hP : IsPushout i j r s) (p : D ⟶ X) {a b : T ⟶ sliceUnder p}
    (hr : a ≫ sliceUnderRestrict p r = b ≫ sliceUnderRestrict p r)
    (hs : a ≫ sliceUnderRestrict p s = b ≫ sliceUnderRestrict p s) : a = b := by
  apply sliceUnderUncurry_injective
  apply (join_left_isPushout hP T).hom_ext
  · have h := congrArg sliceUnderUncurry hr
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_restrict] at h
    exact h
  · have h := congrArg sliceUnderUncurry hs
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_restrict] at h
    exact h

end SerrePositivity.InfinityCategories
