module
public import SerrePositivity.InfinityCategories.HomotopyLimits.Idempotent.SplittingDiagramCocone
public import SerrePositivity.InfinityCategories.HomotopyLimits.Idempotent.IdemCoconeRestriction

public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Idempotent.Coherent
public import SerrePositivity.InfinityCategories.F1.Idempotent.StrongSplittingCones
public import SerrePositivity.InfinityCategories.Core.Idempotent.Walking

/-!
概要：元の強い分裂の同じ全 Idem 余錐は余極限であり、任意の後合成でも余極限。
方針：元の全強分裂図式の余極限余錐を元の Idem 包含へ制限する。
規約：元の図式・余錐・頂点・脚を保持し、余極限の存在を入力に仮定しない。
使われ方：HTT 4.4.5.12〜15、coherent 冪等図式の有効性の一方向。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全図式の余錐を元の冪等包含へ制限すると、指定した同じ全 Idem 余錐を回収する。 -/
lemma StrongSplitting.cocone_restrict {X : SSet.{u}} {d : CoherentIdempotent X}
    (s : StrongSplitting d) :
    ((splittingDiagramCocone s.val).restrict idemInclusion).val = s.cocone.val := by
  change joinMap idemInclusion (𝟙 _) ≫ (walkingFullJoinCocone.val ≫ s.val) =
    walkingJoinCocone.val ≫ s.val
  rw [← Category.assoc, walkingFullJoinCocone_restrict]

/-- 元の強い分裂から構成した同じ全 Idem 余錐そのものは余極限。 -/
lemma StrongSplitting.cocone_isColimit {X : SSet.{u}} [Quasicategory X]
    {d : CoherentIdempotent X} (s : StrongSplitting d) : IsColimitCone s.cocone := by
  rcases s with ⟨F, rfl⟩
  let s : StrongSplitting (idemInclusion ≫ F) := ⟨F, rfl⟩
  have h := (idemCocone_isColimit_iff_restrict (splittingDiagramCocone F)).mp
    (splittingDiagramCocone_isColimit F)
  have he : (splittingDiagramCocone F).restrict idemInclusion = s.cocone :=
    Subtype.ext s.cocone_restrict
  rw [he] at h
  exact h

/-- 強い分裂が与えられた元の coherent 冪等図式は、同じ図式の余極限を持つ。 -/
lemma StrongSplitting.hasColimit {X : SSet.{u}} [Quasicategory X]
    {d : CoherentIdempotent X} (s : StrongSplitting d) : HasColimit d :=
  ⟨s.cocone, s.cocone_isColimit⟩

/-- 冪等完備な quasicategory の元の任意の coherent 冪等図式は余極限を持つ。 -/
lemma IsIdempotentComplete.hasColimit {X : SSet.{u}} [Quasicategory X]
    (hX : IsIdempotentComplete X) (d : CoherentIdempotent X) : HasColimit d := by
  obtain ⟨s⟩ := hX d
  exact s.hasColimit

/-- 元の全 Idem 余錐を任意の関手で後合成しても、同じ余錐は余極限。 -/
lemma StrongSplitting.postcomposeCocone_isColimit {X Y : SSet.{u}} [Quasicategory Y]
    {d : CoherentIdempotent X} (s : StrongSplitting d) (F : X ⟶ Y) :
    IsColimitCone (show JoinCocone (d ≫ F) from
      ⟨s.cocone.val ≫ F, by rw [← Category.assoc, s.cocone.property]⟩) := by
  have he : (show JoinCocone (d ≫ F) from
      ⟨s.cocone.val ≫ F, by rw [← Category.assoc, s.cocone.property]⟩) = (s.map F).cocone :=
    Subtype.ext (s.cocone_map F).symm
  rw [he]
  exact (s.map F).cocone_isColimit

end SerrePositivity.InfinityCategories.F2.Idempotent
