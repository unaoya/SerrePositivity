module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplittingDiagramCocone
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemCoconeRestriction

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Coherent
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingCones
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の強い分裂の同じ全 Idem 余錐は余極限であり、任意の後合成でも余極限。
方針：元の全強分裂図式の余極限余錐を元の Idem 包含へ制限する。
規約：元の図式・余錐・頂点・脚を保持し、余極限の存在を入力に仮定しない。
使われ方：HTT 4.4.5.12〜15、coherent 冪等図式の有効性の一方向。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の全図式の余錐を元の冪等包含へ制限すると、指定した同じ全 Idem 余錐を回収する。 -/
lemma StrongSplitting.cocone_restrict {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splittingDiagramCocone s.val).restrict _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion).val = s.cocone.val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion (𝟙 _) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingFullJoinCocone.val ≫ s.val) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCocone.val ≫ s.val
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingFullJoinCocone_restrict]

/-- 元の強い分裂から構成した同じ全 Idem 余錐そのものは余極限。 -/
lemma StrongSplitting.cocone_isColimit {X : SSet.{u}} [Quasicategory X]
    {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone s.cocone := by
  rcases s with ⟨F, rfl⟩
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion ≫ F) := ⟨F, rfl⟩
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemCocone_isColimit_iff_restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splittingDiagramCocone F)).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splittingDiagramCocone_isColimit F)
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splittingDiagramCocone F).restrict _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion = s.cocone :=
    Subtype.ext s.cocone_restrict
  rw [he] at h
  exact h

/-- 強い分裂が与えられた元の coherent 冪等図式は、同じ図式の余極限を持つ。 -/
lemma StrongSplitting.hasColimit {X : SSet.{u}} [Quasicategory X]
    {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit d :=
  ⟨s.cocone, s.cocone_isColimit⟩

/-- 冪等完備な quasicategory の元の任意の coherent 冪等図式は余極限を持つ。 -/
lemma IsIdempotentComplete.hasColimit {X : SSet.{u}} [Quasicategory X]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit d := by
  obtain ⟨s⟩ := hX d
  exact s.hasColimit

/-- 元の全 Idem 余錐を任意の関手で後合成しても、同じ余錐は余極限。 -/
@[kerodon 0404]
lemma StrongSplitting.postcomposeCocone_isColimit {X Y : SSet.{u}} [Quasicategory Y]
    {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) (F : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (show _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (d ≫ F) from
      ⟨s.cocone.val ≫ F, by rw [← Category.assoc, s.cocone.property]⟩) := by
  have he : (show _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (d ≫ F) from
      ⟨s.cocone.val ≫ F, by rw [← Category.assoc, s.cocone.property]⟩) = (s.map F).cocone :=
    Subtype.ext (s.cocone_map F).symm
  rw [he]
  exact (s.map F).cocone_isColimit

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
