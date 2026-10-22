module

public import SerrePositivity.InfinityCategories.F1.LeftStraighteningBaseChange
public import SerrePositivity.InfinityCategories.F1.LeftFibrationInfinityEquivalence
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：元の left fibration の全空間・底の厳密な同型を、全分類図式の自然同型へ移す。
方針：底上の同型は元の分類関手で送り、底の同型は実際の引き戻しで比較。
規約：各 fiber の値の同型に留めず、全パラメーターの分類図式を比較する。
使われ方：定義に使用した共変 Hom 関手と、元の coslice 射影の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 底上の元の比較自身の前合成同値は、全分類図式の自然同型を与える。 -/
def leftClassification_of_precompositionEquivalence {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q) := by
  have h := VertexIso.map (leftFibrationInfinityVertexIsoOfPrecompositionEquivalence p q
    f hf ef) (leftStraighteningInfinityMap B)
  rw [← leftStraighteningInfinityDiagram_vertex, ← leftStraighteningInfinityDiagram_vertex] at h
  exact h

/-- 底を厳密に保つ元の全空間の同型は、元の全分類図式の自然同型を与える。 -/
def leftClassification_overIso {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (e : E ≅ F) (he : e.hom ≫ q = p) :
    FunctorIso (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q) :=
  leftClassification_of_precompositionEquivalence p q e.hom he
    (isPrecompositionEquivalence_of_iso e)

/-- 元の底と全空間の同型正方形は、全分類図式を元の底への前合成で比較する。 -/
def leftClassification_squareIso {E F B D : SSet.{u}}
    [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) (q : F ⟶ D) [LeftFibration p] [LeftFibration q]
    (e : E ≅ F) (d : B ≅ D) (he : e.hom ≫ q = p ≫ d.hom) :
    FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map d.hom ≫
      leftStraighteningInfinityDiagram q) (leftStraighteningInfinityDiagram p) := by
  have hsq : IsPullback e.hom p q d.hom := IsPullback.of_horiz_isIso ⟨he⟩
  have : LeftFibration (pullback.snd q d.hom) :=
    ⟨leftFibrations.pullback_snd q d.hom (LeftFibration.mem (p := q))⟩
  exact leftStraighteningInfinityDiagram_baseChangeIso q d.hom ≪≫
    (leftClassification_overIso p (pullback.snd q d.hom)
      hsq.isoPullback hsq.isoPullback_hom_snd).symm

end SerrePositivity.InfinityCategories.F2.Compact
