module

public import Mathlib.CategoryTheory.Category.Cat.AsSmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
概要：通常の右 comma の宇宙持ち上げを、持ち上げた圏の右 comma と比較する。
方針：AsSmall の同値と既存の StructuredArrow.post・pre を合成する。
使われ方：HTT §4.3、Kerodon §7.3（Tag 02Y1）の局所右 Kan の係数 universe の接続。
規約：元の局所射影と全射を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 元の関手を、対象と射を同じ上の宇宙へ包んだ通常の関手。 -/
abbrev asSmallLocalFunctor (L : C ⥤ D) : AsSmall.{u + 1} C ⥤ AsSmall.{u + 1} D :=
  AsSmall.down ⋙ L ⋙ AsSmall.up

/-- 右 comma の全対象と全射を、既存の post と pre で持ち上げる。 -/
def asSmallStructuredArrowFunctor (L : C ⥤ D) (t : D) :
    AsSmall.{u + 1} (StructuredArrow t L) ⥤
      StructuredArrow (AsSmall.up.obj t) (asSmallLocalFunctor L) :=
  AsSmall.down ⋙ StructuredArrow.post t L (AsSmall.up : D ⥤ AsSmall.{u + 1} D) ⋙
    StructuredArrow.pre (AsSmall.up.obj t) (AsSmall.up : C ⥤ AsSmall.{u + 1} C)
      (asSmallLocalFunctor L)

/-- 元の三つの同値を合成した比較は、右 comma の全圏の同値である。 -/
instance asSmallStructuredArrowFunctor_isEquivalence (L : C ⥤ D) (t : D) :
    (asSmallStructuredArrowFunctor L t).IsEquivalence := by
  letI : (AsSmall.up : D ⥤ AsSmall.{u + 1} D).IsEquivalence :=
    (AsSmall.equiv (C := D)).isEquivalence_functor
  letI : (AsSmall.up : C ⥤ AsSmall.{u + 1} C).IsEquivalence :=
    (AsSmall.equiv (C := C)).isEquivalence_functor
  letI : (AsSmall.down : AsSmall.{u + 1} (StructuredArrow t L) ⥤ _).IsEquivalence :=
    (AsSmall.equiv (C := StructuredArrow t L)).isEquivalence_inverse
  unfold asSmallStructuredArrowFunctor
  infer_instance

/-- 右 comma の元の局所射影は全関手として厳密に保存される。 -/
lemma asSmallStructuredArrowFunctor_projection (L : C ⥤ D) (t : D) :
    asSmallStructuredArrowFunctor L t ⋙ StructuredArrow.proj (AsSmall.up.obj t)
      (asSmallLocalFunctor L) =
        AsSmall.down ⋙ StructuredArrow.proj t L ⋙ AsSmall.up := rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
