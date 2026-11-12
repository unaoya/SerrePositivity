module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.ShapeOppositeIso
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.OppositeStrongSplitting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LimitColimitOpposite

/-!
概要：指定した元の全 Idem 図式を反転し、反転図式の強い分裂を元へ戻す。
方針：元の Idem と反転の同型で添字を戻し、元の全包含の可換性を使う。
規約：元の全図式の極限を反転図式の余極限へ移す。新しい図式への置き換えで代用しない。
使われ方：HTT 4.4.5.14 の極限から強い分裂への逆方向。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の全 Idem 図式の反転を、元の Idem の指定同型で添字付けした図式。 -/
def oppositeIdempotent {X : SSet.{u}} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X.op :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemOppositeIso.hom ≫ SSet.opFunctor.map d

/-- 指定した元の全図式の極限は、その元の反転図式の余極限を与える。 -/
lemma oppositeIdempotent_hasColimit_of_hasLimit {X : SSet.{u}}
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit d) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (oppositeIdempotent d) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_restrict_of_isIso (SSet.opFunctor.map d) _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemOppositeIso.hom).mp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasLimit_iff_hasColimit_op d).mp hd)

/-- 元の反転図式の強い分裂から、同じ元の全図式の厳密な強い分裂を回収する。 -/
def oppositeIdempotentSplittingToOriginal {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting (oppositeIdempotent d)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.OppositeStrongSplitting.toStrong
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splitOppositeIso.inv ≫ s.val, ?_⟩
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemOppositeIso_inv_inclusion, Category.assoc, s.property]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemOppositeIso.inv_hom_id_assoc (SSet.opFunctor.map d)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
