module

public import SerrePositivity.InfinityCategories.Sheaves.SieveFactorizationLocalCone
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.AsSmallStructuredArrow
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.RightConeTransportPostcomp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.QCatEquivalence

/-!
概要：二段分解の局所 comma の元の全形状を、実右 Kan の添字へ接続する。
方針：Mathlib の左右 comma の反転同値、AsSmall 比較、既存の右 Kan 形状同型を合成する。
  文献対応：HTT 6.2.2.6、Kerodon §7.3（Tag 02Y1）の降下の合成。
規約：元の形状射を固定し、係数の universe を下げない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C}

/-- 元の局所 comma の反転を、Mathlib の既存同値で右 comma へ移す。 -/
abbrev sieveFactorizationLocalOppositeEquivalence (R S : Sieve U) (t : sieveCategory R) :=
  costructuredArrowOpEquivalence (sieveFactorizationOuter R S) t

/-- 元の射影の反転を、係数と同じ上の universe で表示する。 -/
abbrev sieveFactorizationRightKanFunctor (R S : Sieve U) :=
  asSmallLocalFunctor (sieveFactorizationOuter R S).op

/-- 元の局所 comma から、実右 Kan の局所添字への指定比較射。 -/
def sieveFactorizationRightKanShapeComparison (R S : Sieve U) (t : sieveCategory R) :
    presheafShape (sieveFactorizationLocalComma R S t) ⟶
      rightKanShape (nerveMap (sieveFactorizationRightKanFunctor R S))
        (nerveVertex (AsSmall.up.obj (Opposite.op t))) :=
  (nerveAsSmallIso (sieveFactorizationLocalComma R S t)ᵒᵖ).hom ≫
    nerveMap (asSmallLocalFunctor (sieveFactorizationLocalOppositeEquivalence R S t).functor) ≫
      nerveMap (asSmallStructuredArrowFunctor (sieveFactorizationOuter R S).op (Opposite.op t)) ≫
        (nerveRightKanShapeIso (AsSmall.up.obj (Opposite.op t))
          (sieveFactorizationRightKanFunctor R S)).hom

/-- 上の universe に表示した同じ通常同値も、元の全射上の同値である。 -/
private lemma localOppositeAsSmall_isEquivalence (R S : Sieve U) (t : sieveCategory R) :
    (asSmallLocalFunctor (sieveFactorizationLocalOppositeEquivalence R S t).functor).IsEquivalence := by
  let e := sieveFactorizationLocalOppositeEquivalence R S t
  letI : e.functor.IsEquivalence := e.isEquivalence_functor
  letI : (AsSmall.down : AsSmall.{u + 1} (sieveFactorizationLocalComma R S t)ᵒᵖ ⥤ _).IsEquivalence :=
    (AsSmall.equiv (C := (sieveFactorizationLocalComma R S t)ᵒᵖ)).isEquivalence_inverse
  letI : (AsSmall.up : StructuredArrow (Opposite.op t) (sieveFactorizationOuter R S).op ⥤
      AsSmall.{u + 1} _).IsEquivalence :=
    (AsSmall.equiv (C := StructuredArrow (Opposite.op t) (sieveFactorizationOuter R S).op)).isEquivalence_functor
  change (AsSmall.down ⋙ e.functor ⋙ AsSmall.up).IsEquivalence
  infer_instance

/-- 指定した実形状比較射そのものが準圏の同値である。 -/
lemma sieveFactorizationRightKanShapeComparison_isQCatEquivalence (R S : Sieve U)
    (t : sieveCategory R) : IsQCatEquivalence (sieveFactorizationRightKanShapeComparison R S t) := by
  let f := asSmallLocalFunctor (sieveFactorizationLocalOppositeEquivalence R S t).functor
  letI : f.IsEquivalence := localOppositeAsSmall_isEquivalence R S t
  have h1 := (nerveQCatEquivalence f.asEquivalence).isQCatEquivalence
  have h2 := (nerveQCatEquivalence
    (asSmallStructuredArrowFunctor (sieveFactorizationOuter R S).op (Opposite.op t)).asEquivalence).isQCatEquivalence
  exact (qCatEquivalenceOfIso (nerveAsSmallIso (sieveFactorizationLocalComma R S t)ᵒᵖ)).isQCatEquivalence.comp
    (h1.comp (h2.comp (qCatEquivalenceOfIso
      (nerveRightKanShapeIso (AsSmall.up.obj (Opposite.op t))
        (sieveFactorizationRightKanFunctor R S))).isQCatEquivalence))

end SerrePositivity.InfinityCategories.Sheaves
