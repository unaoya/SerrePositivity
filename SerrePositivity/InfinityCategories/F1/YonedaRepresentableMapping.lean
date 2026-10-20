module

public import SerrePositivity.InfinityCategories.F1.YonedaPresheafEvaluation
public import SerrePositivity.InfinityCategories.F1.RepresentablePresheafValues
public import SerrePositivity.InfinityCategories.F1.UniversePinchedHom

/-!
概要：表現可能前層間の写像空間を元の写像空間へ戻し、同じ Yoneda 写像の作用を明示する。
方針：証明済みの Yoneda 評価と値の同値を合成し、実際の Hom 作用の端点と宇宙を正規化する。
規約：比較同値の存在と、Yoneda 写像そのものの充満忠実性を区別する。
使われ方：残る全パラメーターの照合を一つの具体的な自己写像の同値性として扱う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ表現可能前層間の写像空間を、元の標準写像空間へ戻す実際の比較。 -/
def yonedaRepresentableMappingComparison {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) :
    pinchedHom (functorVertex (representablePresheafInfinity x))
      (functorVertex (representablePresheafInfinity y)) ⟶
        (SSet.uliftFunctor.{u + 1, u}).obj (pinchedHom x y) :=
  yonedaPresheafEvaluation x (representablePresheafInfinity y) ≫
    (SSet.uliftFunctor.{u + 1, u}).map (representablePresheafValueEquivalence x y).hom

/-- 上の写像空間比較は、同じ実際の評価を順方向とする同値。 -/
lemma yonedaRepresentableMappingComparison_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    IsQCatEquivalence (yonedaRepresentableMappingComparison x y) :=
  (yonedaPresheafEvaluation_isQCatEquivalence x (representablePresheafInfinity y)).comp
    (representablePresheafValueEquivalence x y).isQCatEquivalence.ulift

/-- 同じ Yoneda 写像の Hom 作用を、元の写像空間の持ち上げから表す。 -/
def yonedaInfinityMappingSpaceMap {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj (pinchedHom x y) ⟶
      pinchedHom (functorVertex (representablePresheafInfinity x))
        (functorVertex (representablePresheafInfinity y)) :=
  (uliftPinchedHomIso x y).hom ≫
    pinchedHomMap (yonedaInfinityMap C) (ULift.up x) (ULift.up y) ≫
    eqToHom (congrArg₂ (fun a b ↦ pinchedHom a b)
      (yonedaInfinityMap_vertex x) (yonedaInfinityMap_vertex y))

/-- 元の写像空間上で、同じ Yoneda 写像の作用の後に恒等点評価を行う自己写像。 -/
def yonedaInfinityEvaluatedMappingSpaceMap {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj (pinchedHom x y) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (pinchedHom x y) :=
  yonedaInfinityMappingSpaceMap x y ≫ yonedaRepresentableMappingComparison x y

/-- 実際の評価後の作用の同値性は、同じ Yoneda 写像の元の Hom 作用の同値性と同値。 -/
lemma yonedaInfinityEvaluatedMappingSpaceMap_isQCatEquivalence_iff
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    IsQCatEquivalence (yonedaInfinityEvaluatedMappingSpaceMap x y) ↔
      IsQCatEquivalence
        (pinchedHomMap (yonedaInfinityMap C) (ULift.up x) (ULift.up y)) := by
  have hU := (qCatEquivalenceOfIso (uliftPinchedHomIso.{u, u + 1} x y)).isQCatEquivalence
  have hE := (qCatEquivalenceOfIso (eqToIso (congrArg₂ (fun a b ↦ pinchedHom a b)
    (yonedaInfinityMap_vertex x) (yonedaInfinityMap_vertex y)))).isQCatEquivalence
  have hV := yonedaRepresentableMappingComparison_isQCatEquivalence x y
  constructor
  · intro h
    exact hE.cancel_right (hU.cancel_left (hV.cancel_right h))
  · intro h
    exact (hU.comp (h.comp hE)).comp hV

/-- 同じ Yoneda 写像の充満忠実性に残る条件を、全ての実際の評価後の作用へ限定する。 -/
lemma yonedaInfinityMap_isFullyFaithful_iff_evaluatedMappingSpace
    (C : SSet.{u}) [Quasicategory C] :
    IsFullyFaithful (yonedaInfinityMap C) ↔
      ∀ x y : C _⦋0⦌, IsQCatEquivalence (yonedaInfinityEvaluatedMappingSpaceMap x y) := by
  constructor
  · intro h x y
    exact (yonedaInfinityEvaluatedMappingSpaceMap_isQCatEquivalence_iff x y).mpr
      (h (ULift.up x) (ULift.up y)).isQCatEquivalence
  · intro h x y
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    exact ((yonedaInfinityEvaluatedMappingSpaceMap_isQCatEquivalence_iff x y).mp
      (h x y)).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
