module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplitOpposite
public import SerrePositivity.InfinityCategories.HTT.Section6_1_2.OppositeIso

/-!
概要：元の全 Idem と分裂添字を、それぞれ元の単体反転と同型にする。
方針：元の反対圏との圏同型を nerve に移し、元の反対 nerve 比較を合成する。
規約：元の全包含の正方形を、同じ単体的写像の厳密な等式で保持する。
使われ方：指定した元の全 Idem 図式の極限から強い分裂を構成する。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の全 Idem と、元の単体反転の指定同型。 -/
def idemOppositeIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape.{u} ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape.op :=
  nerveFunctor.mapIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingIdemOppositeIso ≪≫ _root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem

/-- 元の全分裂添字と、元の単体反転の指定同型。 -/
def splitOppositeIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.{u} ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.op :=
  nerveFunctor.mapIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSplitOppositeIso ≪≫ _root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit

/-- 元の全包含と、元の二つの反転同型の正方形は厳密に可換。 -/
lemma idemOppositeIso_inclusion : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion.{u} ≫ splitOppositeIso.hom =
    idemOppositeIso.hom ≫ SSet.opFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion := by
  have h := congrArg (fun F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}ᵒᵖ ↦ nerveMap F)
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion_toOpposite
  change nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSplitToOpposite =
    nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingIdemToOpposite ≫ nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.op at h
  change (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSplitToOpposite) ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit).hom =
      nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingIdemToOpposite ≫
        ((_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem).hom ≫ SSet.opFunctor.map (nerveMap _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion))
  rw [h, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso_natural]

/-- 元の逆同型の正方形も、同じ全包含と厳密に可換。 -/
lemma idemOppositeIso_inv_inclusion : idemOppositeIso.{u}.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion =
    SSet.opFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion ≫ splitOppositeIso.inv := by
  apply (cancel_mono splitOppositeIso.hom).mp
  rw [Category.assoc, idemOppositeIso_inclusion, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.4.5.13"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemOppositeIso_inclusion
attribute [cite HTT "4.4.5.13"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.splitOppositeIso
