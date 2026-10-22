module

public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemSourceIso
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful

/-!
概要：元の全 Idem 包含は inner fibration であり、元の写像空間で充満忠実。
方針：元の全部分複体との厳密な同型を使い、保存済みの一般定理を移す。
規約：両性質を実際に証明し、元の Kan 延長の未証明の入力として仮定しない。
使われ方：元の coherent 冪等図式への厳密な Kan 延長の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全 Idem 包含そのものは inner fibration。 -/
instance idemInclusion_innerFibration : InnerFibration idemInclusion.{u} where
  mem := by
    rw [← idemSourceIso_inclusion]
    have h : innerFibrations sourceSubcomplex.{u}.ι :=
      @InnerFibration.mem _ _ _ (fullSubcomplexOnVertices_innerFibration SplitShape IsSourceVertex)
    exact innerFibrations.comp_mem _ _ (MorphismProperty.of_isIso innerFibrations _) h

/-- 元の全 Idem 包含は、元の pinched 写像空間で充満忠実。 -/
lemma idemInclusion_isFullyFaithful : IsFullyFaithful idemInclusion.{u} := by
  have : Quasicategory sourceSubcomplex.{u}.toSSet :=
    inferInstanceAs (Quasicategory (fullSubcomplexOnVertices SplitShape IsSourceVertex : SSet.{u}))
  have h : IsFullyFaithful sourceSubcomplex.{u}.ι :=
    isFullyFaithful_fullSubcomplexOnVertices_ι SplitShape IsSourceVertex
  have hi := (qCatEquivalenceOfIso idemSourceIso.{u}).isFullyFaithful
  rw [← idemSourceIso_inclusion]
  exact hi.comp h

end SerrePositivity.InfinityCategories.F2.Idempotent
