module

public import SerrePositivity.InfinityCategories.Sheaves.SpacePresheafOppositeYonedaComparison

/-!
概要：実際の Yoneda と固定された前層の始域・終域を、指定した同型で揃える。
方針：反対 nerve の既存同型を内部 Hom の第一変数で送り、反対を取る。
規約：元の反対 Yoneda と同じ前層形状を保持する。
使われ方：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）の係数移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.Sheaves
variable (C : Type u) [SmallCategory C]

/-- 固定した前層の始域と実際の Yoneda の反対の始域の指定同型。
HTT 5.1.5.6、既存の反対 nerve・宇宙変更の合成則。 -/
def fixedYonedaDomainIso :
    presheafShape C ≅ ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)).op :=
  (SSet.uliftFunctor.{u + 1, u}).mapIso (nerveOppositeIso (C := C)).symm ≪≫
    uliftOppositeIso (nerve C)

/-- 反対 nerve の指定同型に沿った、空間値前層そのものの同型。
HTT 5.1.5.6、内部 Hom の第一変数の同型保存則。 -/
def fixedPresheafShapeIso :
    PresheafInfinity (nerve C) ≅ PresheafCat C SpaceInfinity.{u} :=
  ((internalHom.mapIso
    ((SSet.uliftFunctor.{u + 1, u}).mapIso (nerveOppositeIso (C := C)).symm).op).app
      SpaceInfinity.{u})

/-- 固定形状に移した反対 Yoneda の四角形は、指定した始域・終域の同型で可換。
HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）、同じ射の合成則。 -/
lemma nativeSetShapeOppositeYoneda_square :
    nativeSetShapeOppositeYoneda C ≫
      (SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).inv =
    (fixedYonedaDomainIso C).hom ≫ SSet.opFunctor.map (yonedaInfinityMap (nerve C)) := by
  change (fixedYonedaDomainIso C).hom ≫
      SSet.opFunctor.map (yonedaInfinityMap (nerve C) ≫ (fixedPresheafShapeIso C).hom) ≫
        (SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).inv = _
  have h : SSet.opFunctor.map (fixedPresheafShapeIso C).hom ≫
      (SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).inv = 𝟙 _ :=
    (SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).hom_inv_id
  rw [Functor.map_comp, Category.assoc, h, Category.comp_id]

end SerrePositivity.InfinityCategories.Sheaves
