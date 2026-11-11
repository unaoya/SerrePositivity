module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplittingDiagramCone
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingCones
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の強い分裂の同じ全 Idem 錐は極限であり、任意の後合成でも極限。
方針：元の全強分裂図式の極限錐を元の Idem 包含へ制限する。
規約：元の図式・錐・頂点・脚を保持し、極限の存在を入力に仮定しない。
使われ方：HTT 4.4.5.13〜15、coherent 冪等図式の有効性の一方向。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の全図式の錐を元の冪等包含へ制限すると、指定した同じ全 Idem 錐を回収する。 -/
lemma StrongSplitting.cone_restrict {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splittingDiagramCone s.val) _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion).val = s.cone.val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingFullJoinCone.val ≫ s.val) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCone.val ≫ s.val
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingFullJoinCone_restrict]

/-- 元の強い分裂から構成した同じ全 Idem 錐そのものは極限。 -/
lemma StrongSplitting.cone_isLimit {X : SSet.{u}} [Quasicategory X]
    {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone s.cone := by
  rcases s with ⟨F, rfl⟩
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion ≫ F) := ⟨F, rfl⟩
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemCone_isLimit_iff_restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splittingDiagramCone F)).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splittingDiagramCone_isLimit F)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splittingDiagramCone F) _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion = s.cone :=
    Subtype.ext s.cone_restrict
  rw [he] at h
  exact h

/-- 強い分裂が与えられた元の coherent 冪等図式は、同じ図式の極限を持つ。 -/
lemma StrongSplitting.hasLimit {X : SSet.{u}} [Quasicategory X]
    {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit d :=
  ⟨s.cone, s.cone_isLimit⟩

/-- 冪等完備な quasicategory の元の任意の coherent 冪等図式は極限を持つ。 -/
lemma IsIdempotentComplete.hasLimit {X : SSet.{u}} [Quasicategory X]
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit d := by
  obtain ⟨s⟩ := hX d
  exact s.hasLimit

/-- 元の全 Idem 錐を任意の関手で後合成しても、同じ錐は極限。 -/
@[kerodon 0404]
lemma StrongSplitting.postcomposeCone_isLimit {X Y : SSet.{u}} [Quasicategory Y]
    {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) (F : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (show _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (d ≫ F) from
      ⟨s.cone.val ≫ F, by rw [← Category.assoc, s.cone.property]⟩) := by
  have he : (show _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (d ≫ F) from
      ⟨s.cone.val ≫ F, by rw [← Category.assoc, s.cone.property]⟩) = (s.map F).cone :=
    Subtype.ext (s.cone_map F).symm
  rw [he]
  exact (s.map F).cone_isLimit

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
