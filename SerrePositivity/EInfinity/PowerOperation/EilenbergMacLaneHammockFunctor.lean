module

public import SerrePositivity.EInfinity.PowerOperation.ComplexHammockSource
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneNativeWeak

/-!
# 元の全複体の hammock 局所化から native Sp への実関手

DAG XIII §2.2 の既存 D(A) への降下の前段。準同型の辺を反転する元の図式を
全圏局所化の普遍性で延長し、元の図式へ戻る全関手の同型を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open IsomorphismsAndIsofibrations (isInvertibleEdge_congr)
variable (A : Type u) [CommRing A]

/-- 元の相対圏上で読んだ、同じ厳密な複体図式の EM スペクトルの値。 -/
def complexRelativeSpectrumSource :
    nerve (complexRelativeCategory A).category ⟶ KST.Spectra.Sp.{u} :=
  complexRelativeNerveDown A ≫ eilenbergMacLaneOrdinaryNative A

lemma complexRelativeSpectrumSource_inverts :
    InvertsEdges (complexRelativeSpectrumSource A)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (complexRelativeCategory A)) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges_inverts_of_arrows (complexRelativeCategory A)
  intro X Y f hf
  let := projectiveModelCategory A
  have : QuasiIso ((complexRelativeDown A).map f) := hf
  have h := eilenbergMacLaneOrdinaryNative_map_weak A ((complexRelativeDown A).map f)
  apply (isInvertibleEdge_congr ?_).mp h
  change (eilenbergMacLaneOrdinaryNative A).app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ ((complexRelativeDown A).map f)) =
    (eilenbergMacLaneOrdinaryNative A).app (Opposite.op ⦋1⦌)
      ((complexRelativeNerveDown A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f))
  rw [complexRelativeNerveDown_mk₁]

/-- 同じ全複体の局所化から native Sp への実関手。 -/
def eilenbergMacLaneHammockFunctor : complexHammockNerve A ⟶ KST.Spectra.Sp.{u} :=
  KST.LocalizingInvariants.localizationDescend _ _ (complexHammockSource_isLocalization A)
    (complexRelativeSpectrumSource A) (complexRelativeSpectrumSource_inverts A)

/-- 元の通常複体図式との、全関手を保つ指定同型。 -/
def eilenbergMacLaneHammockFunctor_sourceIso :
    FunctorIso (complexHammockSource A ≫ eilenbergMacLaneHammockFunctor A)
      (complexRelativeSpectrumSource A) :=
  KST.LocalizingInvariants.localizationDescendIso _ _ (complexHammockSource_isLocalization A)
    (complexRelativeSpectrumSource A) (complexRelativeSpectrumSource_inverts A)

end SerrePositivity.EInfinity.PowerOperation
