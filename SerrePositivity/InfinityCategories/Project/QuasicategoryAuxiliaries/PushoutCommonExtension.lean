module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCornerComparison

/-!
概要：共通部分に同じ拡張を付着した二つの対象を貼り合わせる。
方針：各 pushout の普遍性を二回使って、元の貼り合わせへの付着と比較する。
規約：任意の圏の指定された射を保持し、単射性は要求しない。
使われ方：有限形状の余極限構成で、共有する部分余極限頂点を一度だけ付加する。
-/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace PushoutCommonExtension
variable {C : Type u} [Category.{v} C] [HasPushouts C]
variable {A B D V : C} (f : A ⟶ B) (g : A ⟶ D) (a : A ⟶ V)

/-- 共通拡張後の二対象を貼り合わせた形状。 -/
abbrev Target := pushout (pushout.inr f a) (pushout.inr g a)

/-- 元の貼り合わせから共通拡張後の貼り合わせへの実比較。 -/
def map : pushout f g ⟶ Target f g a :=
  pushout.desc (pushout.inl f a ≫ pushout.inl _ _)
    (pushout.inl g a ≫ pushout.inr _ _) (by
      calc
        _ = a ≫ pushout.inr f a ≫ pushout.inl _ _ := pushout.condition_assoc _
        _ = a ≫ pushout.inr g a ≫ pushout.inr _ _ :=
          congrArg (a ≫ ·) pushout.condition
        _ = _ := (pushout.condition_assoc _).symm)

/-- 共通拡張の包含。 -/
def inclusion : V ⟶ Target f g a := pushout.inr f a ≫ pushout.inl _ _

/-- 元の共通部分上の比較の整合性。 -/
lemma comm : a ≫ inclusion f g a = (f ≫ pushout.inl f g) ≫ map f g a := by
  simp only [inclusion, map, Category.assoc, pushout.inl_desc]
  exact (pushout.condition_assoc _).symm

/-- 共通拡張後の貼り合わせは、元の貼り合わせへ共通拡張を付加した pushout。 -/
lemma isPushout : IsPushout a (f ≫ pushout.inl f g) (inclusion f g a) (map f g a) := by
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk (comm f g a) ?_ ?_ ?_ ?_)
  · intro s
    let l := pushout.desc (pushout.inl f g ≫ s.inr) s.inl (by
      simpa only [← Category.assoc] using s.condition.symm)
    let r := pushout.desc (pushout.inr f g ≫ s.inr) s.inl (by
      rw [← Category.assoc, ← pushout.condition]
      simpa only [Category.assoc] using s.condition.symm)
    exact pushout.desc l r (by simp only [l, r, pushout.inr_desc])
  · intro s
    simp only [inclusion, Category.assoc, pushout.inl_desc, pushout.inr_desc]
  · intro s
    apply pushout.hom_ext
    · simp only [map, pushout.inl_desc_assoc, Category.assoc,
        pushout.inl_desc, pushout.inl_desc_assoc]
    · simp only [map, pushout.inr_desc_assoc, Category.assoc,
        pushout.inr_desc, pushout.inl_desc]
  · intro s m hm hn
    apply pushout.hom_ext
    · apply pushout.hom_ext
      · simpa only [map, pushout.inl_desc_assoc, Category.assoc,
          pushout.inl_desc] using congrArg (pushout.inl f g ≫ ·) hn
      · simpa only [inclusion, Category.assoc, pushout.inl_desc,
          pushout.inr_desc] using hm
    · apply pushout.hom_ext
      · simpa only [map, pushout.inr_desc_assoc, Category.assoc,
          pushout.inr_desc, pushout.inl_desc] using congrArg (pushout.inr f g ≫ ·) hn
      · simpa only [inclusion, Category.assoc, pushout.inr_desc,
          pushout.condition_assoc] using hm

end PushoutCommonExtension
end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
