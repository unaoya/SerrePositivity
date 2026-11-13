module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.PushoutCornerComparison

/-!
概要：pushout の片側を拡大する比較は、その片側の射の pushout。
方針：元の pushout と拡大後の外側の pushout から片側を消去する。
規約：単射性や特別な圏を仮定しない。
使われ方：二つの部分余極限を順に付加して全形状の余極限を比較する。
-/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
variable {C : Type u} [Category.{v} C] [HasPushouts C]
variable {A B D B' D' : C} (f : A ⟶ B) (g : A ⟶ D)

/-- pushout の左側の対象を拡大する実比較。 -/
def pushoutLeftExpansion (b : B ⟶ B') : pushout f g ⟶ pushout (f ≫ b) g :=
  pushout.desc (b ≫ pushout.inl _ _) (pushout.inr _ _) (by
    rw [← Category.assoc]
    exact pushout.condition)

/-- 左側の拡大の比較は、元の左側の射の pushout。 -/
lemma pushoutLeftExpansion_isPushout (b : B ⟶ B') :
    IsPushout b (pushout.inl f g) (pushout.inl (f ≫ b) g)
      (pushoutLeftExpansion f g b) := by
  have ho : IsPushout (f ≫ b) g (pushout.inl (f ≫ b) g)
      (pushout.inr f g ≫ pushoutLeftExpansion f g b) := by
    simpa only [pushoutLeftExpansion, pushout.inr_desc] using
      (IsPushout.of_hasPushout (f ≫ b) g)
  exact ho.of_left (pushout.inl_desc _ _ _).symm (IsPushout.of_hasPushout f g)

/-- pushout の右側の対象を拡大する実比較。 -/
def pushoutRightExpansion (d : D ⟶ D') : pushout f g ⟶ pushout f (g ≫ d) :=
  pushout.desc (pushout.inl _ _) (d ≫ pushout.inr _ _) (by
    rw [← Category.assoc]
    exact pushout.condition)

/-- 右側の拡大の比較は、元の右側の射の pushout。 -/
lemma pushoutRightExpansion_isPushout (d : D ⟶ D') :
    IsPushout d (pushout.inr f g) (pushout.inr f (g ≫ d))
      (pushoutRightExpansion f g d) := by
  have ho : IsPushout (g ≫ d) f (pushout.inr f (g ≫ d))
      (pushout.inl f g ≫ pushoutRightExpansion f g d) := by
    simpa only [pushoutRightExpansion, pushout.inl_desc] using
      (IsPushout.of_hasPushout f (g ≫ d)).flip
  exact ho.of_left (pushout.inr_desc _ _ _).symm (IsPushout.of_hasPushout f g).flip

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
