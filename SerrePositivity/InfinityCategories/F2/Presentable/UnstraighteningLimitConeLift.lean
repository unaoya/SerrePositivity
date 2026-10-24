module

public import SerrePositivity.InfinityCategories.F2.Presentable.CosliceLimitConeLift
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeValEquality

/-!
概要：空間値関手が保つ底の極限錐を元の left unstraightening へ持ち上げる。
方針：点付き空間での coslice 錐の持ち上げと元の引き戻しを合成する。
規約：底の全錐と元の全図式を厳密に保持する。
使われ方：随伴関手定理の小さい解図式の極限から点付き解対象を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：関手が底の錐を極限へ送れば元の全図式は同じ底の錐上の全錐を持つ。
方針：図式の点付き成分の錐を作り、指定した底の錐と引き戻しに束ねる。
規約：底の極限性は関手による像の極限性にのみ必要であり、別の錐へ置き換えない。
使われ方：解対象の存在と後続の compact な対象への因子化。 -/
lemma exists_unstraighteningCone_lift_of_map_isLimit
    {K C : SSet.{u + 1}} (F : C ⟶ SpaceInfinity.{u})
    (D : K ⟶ leftUnstraightening F)
    (c : JoinCone (D ≫ leftUnstraighteningProjection F))
    (hc : IsLimitCone (mapJoinCone F c)) :
    ∃ d : JoinCone D, d.val ≫ leftUnstraighteningProjection F = c.val := by
  let g := D ≫ pullback.fst pointedSpaceProjection F
  let cF : JoinCone (g ≫ pointedSpaceProjection) := ⟨c.val ≫ F, by
    rw [← Category.assoc, c.property]
    change (D ≫ pullback.snd pointedSpaceProjection F) ≫ F =
      (D ≫ pullback.fst pointedSpaceProjection F) ≫ pointedSpaceProjection
    rw [Category.assoc, Category.assoc, pullback.condition]⟩
  have hcF : IsLimitCone cF :=
    (F2.isLimitCone_iff_of_cone_val_eq (mapJoinCone F c) cF rfl).mp hc
  obtain ⟨dF, hdF⟩ := exists_cosliceCone_lift_of_isLimit g cF hcF
  let d : JoinCone D := ⟨pullback.lift dF.val c.val hdF, by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact dF.property
    · rw [Category.assoc, pullback.lift_snd]
      exact c.property⟩
  exact ⟨d, pullback.lift_snd _ _ _⟩

end SerrePositivity.InfinityCategories.F2.Presentable
