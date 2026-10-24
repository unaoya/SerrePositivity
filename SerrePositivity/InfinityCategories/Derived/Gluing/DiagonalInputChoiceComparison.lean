module
public import SerrePositivity.InfinityCategories.Derived.Gluing.InputHomotopyClassComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomDiagonalDeformations
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomDiagonalComparisonBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyTriangleFillingCriterion

/-! # 入力固定変形から共通対角の指定辺への移送

概要：実入力固定変形の対角辺と、選択済みの正本対角辺の類を比較する。
方針：実自明 Kan 射影の忠実性を使い、対角への後合成と端点の表示変更を行う。
規約：両端の等式だけでなく全時間の入力射影の一致を要求する。
使われ方：貼り合わせから得る二変形を指定三角形境界の辺へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed DifferentialGraded SSet

lemma dgGluingHomotopyRetarget_homMk_eq {A Z : SSet.{u}}
    {f g f' g' : A ⟶ Z} (H G : SSet.Homotopy f g) (hf : f = f') (hg : g = g')
    (h : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy G)) :
    SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (stableHomotopyRetarget H hf hg)) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (stableHomotopyRetarget G hf hg)) := by
  subst f'
  subst g'
  exact h

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

def dgGluingLaxHomFirstDiagonalHomotopyOfInput
    (H : SSet.Homotopy (dgGluingLaxHomFirstCompositionInputLift R C D M X Y)
      (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y)) :=
  stableHomotopyRetarget
    (functorHomotopyPostcomp H (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y))
    (dgGluingLaxHomCommonDiagonal_first R C D M X Y).symm
    (dgGluingHomDerivedFirstCompositionInputLift_diagonal R C D M X Y)

def dgGluingLaxHomLastDiagonalHomotopyOfInput
    (H : SSet.Homotopy (dgGluingLaxHomLastCompositionInputLift R C D M X Y)
      (dgGluingHomDerivedLastCompositionInputLift R C D M X Y)) :=
  stableHomotopyRetarget
    (functorHomotopyPostcomp H (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)) rfl
    (dgGluingHomDerivedLastCompositionInputLift_diagonal R C D M X Y)

lemma dgGluingLaxHomFirstDiagonalHomotopyOfInput_class
    (H : SSet.Homotopy (dgGluingLaxHomFirstCompositionInputLift R C D M X Y)
      (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y))
    (hH : H.h ≫ dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      (dgGluingLaxHomFirstInputHomotopy R C D M X Y).h ≫
        dgGluingDerivedFirstCompositionInputProjection R C D M X Y) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingLaxHomFirstDiagonalHomotopyOfInput R C D M X Y H)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y)) := by
  apply dgGluingHomotopyRetarget_homMk_eq
  have h := congrArg
    ((hoFunctor.map ((ihom _).map
      (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y))).toFunctor.map)
    (dgGluingLaxHomFirstInputHomotopy_class_independent R C D M X Y H hH)
  change SSet.Truncated.HomotopyCategory.homMk
      ((functorEdgeOfSimplicialHomotopy H).map ((truncation 2).map _)) =
    SSet.Truncated.HomotopyCategory.homMk
      ((functorEdgeOfSimplicialHomotopy _).map ((truncation 2).map _)) at h
  simpa only [dgGluingFunctorHomotopyPostcomp_edge] using h

lemma dgGluingLaxHomLastDiagonalHomotopyOfInput_class
    (H : SSet.Homotopy (dgGluingLaxHomLastCompositionInputLift R C D M X Y)
      (dgGluingHomDerivedLastCompositionInputLift R C D M X Y))
    (hH : H.h ≫ dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      (dgGluingLaxHomLastInputHomotopy R C D M X Y).h ≫
        dgGluingDerivedLastCompositionInputProjection R C D M X Y) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingLaxHomLastDiagonalHomotopyOfInput R C D M X Y H)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingLaxHomLastDiagonalHomotopy R C D M X Y)) := by
  apply dgGluingHomotopyRetarget_homMk_eq
  have h := congrArg
    ((hoFunctor.map ((ihom _).map
      (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y))).toFunctor.map)
    (dgGluingLaxHomLastInputHomotopy_class_independent R C D M X Y H hH)
  change SSet.Truncated.HomotopyCategory.homMk
      ((functorEdgeOfSimplicialHomotopy H).map ((truncation 2).map _)) =
    SSet.Truncated.HomotopyCategory.homMk
      ((functorEdgeOfSimplicialHomotopy _).map ((truncation 2).map _)) at h
  simpa only [dgGluingFunctorHomotopyPostcomp_edge] using h

lemma dgGluingLaxHomDiagonalComparisonBoundary_filling_of_input_triangle
    (Hfirst : SSet.Homotopy (dgGluingLaxHomFirstCompositionInputLift R C D M X Y)
      (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y))
    (Hlast : SSet.Homotopy (dgGluingLaxHomLastCompositionInputLift R C D M X Y)
      (dgGluingHomDerivedLastCompositionInputLift R C D M X Y))
    (hfirst : Hfirst.h ≫ dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      (dgGluingLaxHomFirstInputHomotopy R C D M X Y).h ≫
        dgGluingDerivedFirstCompositionInputProjection R C D M X Y)
    (hlast : Hlast.h ≫ dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      (dgGluingLaxHomLastInputHomotopy R C D M X Y).h ≫
        dgGluingDerivedLastCompositionInputProjection R C D M X Y)
    (T : FunctorCompositionTriangle
      (dgGluingLaxHomLastDiagonalHomotopyOfInput R C D M X Y Hlast)
      (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y)
      (dgGluingLaxHomFirstDiagonalHomotopyOfInput R C D M X Y Hfirst)) :
    ∃ V, (boundary 2).ι ≫ V = dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y := by
  have h := dgGluingFunctorCompositionTriangle_homEq T
  rw [dgGluingLaxHomLastDiagonalHomotopyOfInput_class R C D M X Y Hlast hlast,
    dgGluingLaxHomFirstDiagonalHomotopyOfInput_class R C D M X Y Hfirst hfirst] at h
  exact dgGluingHomotopyTriangleFilling_of_homEq h

end SerrePositivity.InfinityCategories
