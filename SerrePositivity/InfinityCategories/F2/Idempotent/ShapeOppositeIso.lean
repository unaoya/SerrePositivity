module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingSplitOpposite
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.OppositeIso

/-!
概要：元の全 Idem と分裂添字を、それぞれ元の単体反転と同型にする。
方針：元の反対圏との圏同型を nerve に移し、元の反対 nerve 比較を合成する。
規約：元の全包含の正方形を、同じ単体的写像の厳密な等式で保持する。
使われ方：指定した元の全 Idem 図式の極限から強い分裂を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全 Idem と、元の単体反転の指定同型。 -/
def idemOppositeIso : IdemShape.{u} ≅ IdemShape.op :=
  nerveFunctor.mapIso walkingIdemOppositeIso ≪≫ SerrePositivity.InfinityCategories.F1B.nerveOppositeIso WalkingIdem

/-- 元の全分裂添字と、元の単体反転の指定同型。 -/
def splitOppositeIso : SplitShape.{u} ≅ SplitShape.op :=
  nerveFunctor.mapIso walkingSplitOppositeIso ≪≫ SerrePositivity.InfinityCategories.F1B.nerveOppositeIso WalkingSplit

/-- 元の全包含と、元の二つの反転同型の正方形は厳密に可換。 -/
lemma idemOppositeIso_inclusion : idemInclusion.{u} ≫ splitOppositeIso.hom =
    idemOppositeIso.hom ≫ SSet.opFunctor.map idemInclusion := by
  have h := congrArg (fun F : WalkingIdem.{u} ⥤ WalkingSplit.{u}ᵒᵖ ↦ nerveMap F)
    walkingInclusion_toOpposite
  change nerveMap walkingInclusion ≫ nerveMap walkingSplitToOpposite =
    nerveMap walkingIdemToOpposite ≫ nerveMap walkingInclusion.op at h
  change (nerveMap walkingInclusion ≫ nerveMap walkingSplitToOpposite) ≫
    (SerrePositivity.InfinityCategories.F1B.nerveOppositeIso WalkingSplit).hom =
      nerveMap walkingIdemToOpposite ≫
        ((SerrePositivity.InfinityCategories.F1B.nerveOppositeIso WalkingIdem).hom ≫ SSet.opFunctor.map (nerveMap walkingInclusion))
  rw [h, Category.assoc, SerrePositivity.InfinityCategories.F1B.nerveOppositeIso_natural]

/-- 元の逆同型の正方形も、同じ全包含と厳密に可換。 -/
lemma idemOppositeIso_inv_inclusion : idemOppositeIso.{u}.inv ≫ idemInclusion =
    SSet.opFunctor.map idemInclusion ≫ splitOppositeIso.inv := by
  apply (cancel_mono splitOppositeIso.hom).mp
  rw [Category.assoc, idemOppositeIso_inclusion, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.InfinityCategories.F2.Idempotent
