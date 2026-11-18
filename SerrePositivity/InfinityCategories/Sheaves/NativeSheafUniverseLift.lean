module

public import SerrePositivity.InfinityCategories.Sheaves.NativeSiteDescent
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseLimits

/-!
概要：同じ通常のsiteのnativeな被覆篩の全錐を、同じ持ち上げた層条件と比較する。
方針：元の篩錐と係数射の持ち上げの可換性、既存の極限性の宇宙不変性を使う。
規約：HTT 6.2.2.6の小さい通常のsiteのČech層に関する、既存構成の宇宙移送の法則。
  Kerodon §7.1（Tag 02H1）。presentable性や新しい極限の存在を仮定しない。
使われ方：S8 の任意の係数を表現可能な空間値へ移す際、元の被覆錐の指定を保つ。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u}}

/-- 元の篩錐の持ち上げは、同じ係数射を持ち上げた篩錐と全射が一致する。 -/
lemma nativeRestrictionCone_ulift_val (F : nerve Cᵒᵖ ⟶ E) {U : C} (S : Sieve U) :
    (JoinCone.ulift.{u, u + 1} (nativeRestrictionCone F S)).val =
      (restrictionCone ((SSet.uliftFunctor.{u + 1, u}).map F) S).val := by
  rfl

/-- 同じ元の被覆篩の全錐による層条件は、係数と形状の持ち上げで保存・反映される。 -/
lemma nativeIsSheaf_iff_isSheaf_ulift (J : GrothendieckTopology C) (F : nerve Cᵒᵖ ⟶ E) :
    NativeIsSheaf J F ↔ IsSheaf J ((SSet.uliftFunctor.{u + 1, u}).map F) := by
  have h : ∀ (U : C) (S : Sieve U),
      IsLimitCone (nativeRestrictionCone F S) ↔
        IsLimitCone (restrictionCone ((SSet.uliftFunctor.{u + 1, u}).map F) S) := by
    intro U S
    exact (isLimitCone_iff_ulift (nativeRestrictionCone F S)).trans
      (isLimitCone_iff_of_cone_val_eq _ _ (nativeRestrictionCone_ulift_val F S))
  constructor
  · intro hF U S hS
    exact (h U S).mp (hF U S hS)
  · intro hF U S hS
    exact (h U S).mpr (hF U S hS)

end SerrePositivity.InfinityCategories.Sheaves
