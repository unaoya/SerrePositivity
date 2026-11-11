module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInput
public import SerrePositivity.KST.SConstruction.DGHomGluingTargetContraction
public import SerrePositivity.KST.LocalizingInvariants.DGFixedNullSquare

/-!
概要：恒等 Hom gluing の同じ対角・実 cone 差から、固定 S の実零化面を構成する。
方針：恒等閉比較の実 cone の指定収縮を、全像小模型と宇宙持ち上げで保持する。
規約：対象別収縮を使う商延長であり、自然な収縮や Verdier 認証は仮定しない。
使われ方：LT 全長方形の右面と、その固定 ν 像の全境界比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (u + 1)) [DGCategory R C]
  [Small.{u} C]
local notation "I" => DGFunctor.id (C)
local notation "L" => DGIdentityHomGluing R C
local notation "D" => DGIdentityHomGluingDifference R C

/-- 概要：同じ strict 対角の実閉比較は恒等そのもの。
方針：比較対象の閉射回収を元の恒等四角形に特殊化する。
規約：同型類でなく閉射の等号。使われ方：同じ実 cone の収縮。 -/
lemma dgIdentityHomGluingDiagonal_targetMap (x : C) :
    dgHomGluingTargetMap R (C) (C) (C) (I) (I)
      ((dgIdentityHomGluingDiagonal R C).obj x) =
        𝟙 (ForgetEnrichment.of (Complex R) x) := by
  exact dgHomGluingTargetMap_comparisonObject R (C) (C) (C) (I) (I) (I) (I)
    (dgStrictSquareClosedComparison R (C) (C) (C) (I) (I) (I) (I) rfl) x

/-- 概要：同じ対角像の実 cone における指定次数 −1 元。
方針：恒等比較の既存収縮を同じ全像小模型で使用する。
規約：像対象を選び直さない。使われ方：全対象商の延長データ。 -/
def dgIdentityHomGluingContractingElement (x : C) :
    GradedHom R ((dgIdentityHomGluingDifference R C).obj
      ((dgIdentityHomGluingDiagonal R C).obj x))
      ((dgIdentityHomGluingDifference R C).obj
        ((dgIdentityHomGluingDiagonal R C).obj x)) (-1) :=
  dgHomGluingTargetConeContractingElement R (C) (C) (C) (I) (I)
    ((dgIdentityHomGluingDiagonal R C).obj x) (Iso.refl _)
    (dgIdentityHomGluingDiagonal_targetMap R C x)

/-- 概要：同じ小模型内の指定収縮元の微分は同じ像の恒等元。
方針：全 Hom を保持する包含の定義から既存の微分式を使用する。
規約：同じ実 cone の式。使われ方：固定 S の指定収縮付き合成。 -/
lemma dgIdentityHomGluingContractingElement_d (x : C) :
    (homObject R (D) ((dgIdentityHomGluingDifference R C).obj
      ((dgIdentityHomGluingDiagonal R C).obj x))
      ((dgIdentityHomGluingDifference R C).obj
        ((dgIdentityHomGluingDiagonal R C).obj x))).d (-1) 0
      (dgIdentityHomGluingContractingElement R C x) =
        (unitElement R ((dgIdentityHomGluingDifference R C).obj
          ((dgIdentityHomGluingDiagonal R C).obj x))).val :=
  dgHomGluingTargetConeContractingElement_d R (C) (C) (C) (I) (I)
    ((dgIdentityHomGluingDiagonal R C).obj x) (Iso.refl _)
    (dgIdentityHomGluingDiagonal_targetMap R C x)

/-- 概要：同じ固定 S の対角・差の合成に指定収縮を与える。
方針：対象宇宙を持ち上げても元の全 Hom と微分を使用する。
規約：自然な収縮を仮定しない。使われ方：Sp 正本の実零化面構成。 -/
def dgIdentityHomGluingContracted : DGQuotient.ContractedFunctor R
    (dgIdentityHomGluingBaseInput R C) Set.univ
    (dgIdentityHomGluingDifferenceInput R C) where
  toDGFunctor := (dgIdentityHomGluingDiagonalInputMap R C).down.comp
    (dgIdentityHomGluingDifferenceInputMap R C).down
  homotopy x := dgIdentityHomGluingContractingElement R C x.val.label.down
  d_homotopy x := dgIdentityHomGluingContractingElement_d R C x.val.label.down

/-- 概要：恒等 Hom gluing の元の四辺を持つ固定 S の実零化面。
方針：指定収縮の同じ全対象商延長を使用する。
規約：ν 像の列認証は別に行う。使われ方：LT 長方形の右面。 -/
def dgIdentityHomGluingNullSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R :=
  (exists_dgFixedNullSquare R (dgIdentityHomGluingDiagonalInputMap R C)
    (dgIdentityHomGluingDifferenceInputMap R C)
    (dgIdentityHomGluingContracted R C) rfl).choose

/-- 概要：同じ実零化面の四辺は元の対角・差・商包含・商延長。
方針：同じ選択された面の境界を回収する。
規約：全一単体の等号を保持する。使われ方：指定全境界での貼合せ。 -/
lemma dgIdentityHomGluingNullSquare_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgIdentityHomGluingNullSquare R C = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingDiagonalInputMap R C)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgIdentityHomGluingNullSquare R C = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgIdentityHomGluingDifferenceInputMap R C)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgIdentityHomGluingNullSquare R C = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
          (dgFixedNullLeft R (A := dgIdentityHomGluingBaseInput R C))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgIdentityHomGluingNullSquare R C = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R (dgIdentityHomGluingContracted R C))).edge :=
  (exists_dgFixedNullSquare R (dgIdentityHomGluingDiagonalInputMap R C)
    (dgIdentityHomGluingDifferenceInputMap R C)
    (dgIdentityHomGluingContracted R C) rfl).choose_spec

end SerrePositivity.KST.SConstruction
