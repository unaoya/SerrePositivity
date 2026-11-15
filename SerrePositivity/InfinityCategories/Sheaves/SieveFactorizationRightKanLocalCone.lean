module

public import SerrePositivity.InfinityCategories.Sheaves.SieveFactorizationRightKanData

/-!
概要：二段分解の元の局所錐を、指定右 Kan 輸送の通常の局所錐として回収する。
方針：左右 comma の既存反転同値と AsSmall 比較で、同じ全三角形を照合する。
使われ方：HTT 6.2.2.6、Kerodon §7.3（Tag 02Y1）の降下の合成。
規約：元の余単位・頂点・全脚を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C}

/-- 元の反転した局所 comma を、上の universe の通常の右 comma へ送る。 -/
def sieveFactorizationRightKanCommaComparison (R S : Sieve U) (t : sieveCategory R) :
    AsSmall.{u + 1} (sieveFactorizationLocalComma R S t)ᵒᵖ ⥤
      StructuredArrow (AsSmall.up.obj (Opposite.op t)) (sieveFactorizationRightKanFunctor R S) :=
  asSmallLocalFunctor (sieveFactorizationLocalOppositeEquivalence R S t).functor ⋙
    asSmallStructuredArrowFunctor (sieveFactorizationOuter R S).op (Opposite.op t)

/-- 元の実形状比較は、この通常の右 comma 比較の nerve を通る同じ合成射。 -/
lemma sieveFactorizationRightKanShapeComparison_factor (R S : Sieve U)
    (t : sieveCategory R) :
    sieveFactorizationRightKanShapeComparison R S t =
      (nerveAsSmallIso (sieveFactorizationLocalComma R S t)ᵒᵖ).hom ≫
        nerveMap (sieveFactorizationRightKanCommaComparison R S t) ≫
          (nerveRightKanShapeIso (AsSmall.up.obj (Opposite.op t))
            (sieveFactorizationRightKanFunctor R S)).hom := by
  unfold sieveFactorizationRightKanShapeComparison sieveFactorizationRightKanCommaComparison
  have h : nerveMap (asSmallLocalFunctor (sieveFactorizationLocalOppositeEquivalence R S t).functor ⋙
      asSmallStructuredArrowFunctor (sieveFactorizationOuter R S).op (Opposite.op t)) =
        nerveMap (asSmallLocalFunctor (sieveFactorizationLocalOppositeEquivalence R S t).functor) ≫
          nerveMap (asSmallStructuredArrowFunctor (sieveFactorizationOuter R S).op (Opposite.op t)) :=
    nerveFunctor.map_comp
      (asSmallLocalFunctor (sieveFactorizationLocalOppositeEquivalence R S t).functor).toCatHom
      (asSmallStructuredArrowFunctor (sieveFactorizationOuter R S).op (Opposite.op t)).toCatHom
  rw [h]
  simp only [Category.assoc]

/-- 通常の局所錐の全三角形は、元の局所錐の同じ AsSmall 表示に一致する。 -/
lemma sieveFactorizationRightKanCommaComparison_cone (R S : Sieve U)
    (t : sieveCategory R) :
    ((Functor.RightExtension.mk (sieveFactorizationRightKanTarget R)
      (sieveFactorizationRightKanCounit R S)).coneAt
        (AsSmall.up.obj (Opposite.op t))).whisker
          (sieveFactorizationRightKanCommaComparison R S t) =
      asSmallCone (sieveFactorizationLocalCone R S t) := rfl

end SerrePositivity.InfinityCategories.Sheaves
