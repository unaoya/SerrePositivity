module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitSpanRelativeComparison
/-! # 実単位補正と選択済み二変形の三角形

概要：入力固定の相対充填を、三辺を保持する実合成三角形として公開する。
方針：指定境界から三面を回収し、対角後合成にも三面を保つ。
規約：実補正道と選択済み変形の代表を変更しない。
使われ方：高次貼り合わせの四補正辺を、正本対角三辺の合成等式へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
def dgGluingFunctorCompositionTriangleOfBoundary {K E : SSet.{u}} {f g h : K ⟶ E}
    {l : SSet.Homotopy f g} {r : SSet.Homotopy g h} {d : SSet.Homotopy f h}
    (T : (Δ[2] : SSet.{u}) ⟶ (ihom K).obj E)
    (hT : (boundary 2).ι ≫ T = dgGluingHomotopyTriangleBoundary l r d) :
    FunctorCompositionTriangle l r d where
  diagram := T
  face_zero := by
    have h := congrArg (fun q => boundary.ι (0 : Fin 3) ≫ q) hT
    simpa only [← Category.assoc, boundary.ι_ι,
      dgGluingHomotopyTriangleBoundary_zero] using h
  face_one := by
    have h := congrArg (fun q => boundary.ι (1 : Fin 3) ≫ q) hT
    simpa only [← Category.assoc, boundary.ι_ι,
      dgGluingHomotopyTriangleBoundary_one] using h
  face_two := by
    have h := congrArg (fun q => boundary.ι (2 : Fin 3) ≫ q) hT
    simpa only [← Category.assoc, boundary.ι_ι,
      dgGluingHomotopyTriangleBoundary_two] using h

def dgGluingFunctorCompositionTrianglePostcomp {K E Z : SSet.{u}} {f g h : K ⟶ E}
    {l : SSet.Homotopy f g} {r : SSet.Homotopy g h} {d : SSet.Homotopy f h}
    (T : FunctorCompositionTriangle l r d) (q : E ⟶ Z) :
    FunctorCompositionTriangle (functorHomotopyPostcomp l q)
      (functorHomotopyPostcomp r q) (functorHomotopyPostcomp d q) where
  diagram := T.diagram ≫ (ihom K).map q
  face_zero := by rw [← Category.assoc, T.face_zero, ← curry_natural_right]; rfl
  face_one := by rw [← Category.assoc, T.face_one, ← curry_natural_right]; rfl
  face_two := by rw [← Category.assoc, T.face_two, ← curry_natural_right]; rfl
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

def dgGluingFirstUnitSpanTriangle : FunctorCompositionTriangle
    (dgGluingPreCollarSpanHomotopy R C D M X Y) (dgGluingLaxHomFirstInputHomotopy R C D M X Y)
    (dgGluingPreCapSpanHomotopy R C D M X Y) :=
  dgGluingFunctorCompositionTriangleOfBoundary
    (Classical.choose (dgGluingFirstUnitSpan_relative_filling R C D M X Y))
    (Classical.choose_spec (dgGluingFirstUnitSpan_relative_filling R C D M X Y)).1

lemma dgGluingFirstUnitSpan_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingPreCollarSpanHomotopy R C D M X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingLaxHomFirstInputHomotopy R C D M X Y)) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingPreCapSpanHomotopy R C D M X Y)) :=
  dgGluingFunctorCompositionTriangle_homEq (dgGluingFirstUnitSpanTriangle R C D M X Y)

def dgGluingFirstUnitSpanDiagonalTriangle :=
  dgGluingFunctorCompositionTrianglePostcomp (dgGluingFirstUnitSpanTriangle R C D M X Y)
    (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)

def dgGluingLastUnitSpanTriangle : FunctorCompositionTriangle
    (dgGluingLaxHomLastInputHomotopy R C D M X Y) (dgGluingExitCapSpanHomotopy R C D M X Y)
    (dgGluingExitCollarSpanHomotopy R C D M X Y) :=
  dgGluingFunctorCompositionTriangleOfBoundary
    (Classical.choose (dgGluingLastUnitSpan_relative_filling R C D M X Y))
    (Classical.choose_spec (dgGluingLastUnitSpan_relative_filling R C D M X Y)).1

lemma dgGluingLastUnitSpan_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingLaxHomLastInputHomotopy R C D M X Y)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingExitCapSpanHomotopy R C D M X Y)) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgGluingExitCollarSpanHomotopy R C D M X Y)) :=
  dgGluingFunctorCompositionTriangle_homEq (dgGluingLastUnitSpanTriangle R C D M X Y)

def dgGluingLastUnitSpanDiagonalTriangle :=
  dgGluingFunctorCompositionTrianglePostcomp (dgGluingLastUnitSpanTriangle R C D M X Y)
    (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)

lemma dgGluingFirstUnitSpanTriangle_over :
    (dgGluingFirstUnitSpanTriangle R C D M X Y).diagram ≫
      (ihom _).map (dgGluingDerivedFirstCompositionInputProjection R C D M X Y) =
      SSet.const (functorVertex ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)))) :=
  (Classical.choose_spec (dgGluingFirstUnitSpan_relative_filling R C D M X Y)).2

lemma dgGluingLastUnitSpanTriangle_over :
    (dgGluingLastUnitSpanTriangle R C D M X Y).diagram ≫
      (ihom _).map (dgGluingDerivedLastCompositionInputProjection R C D M X Y) =
      SSet.const (functorVertex ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)))) :=
  (Classical.choose_spec (dgGluingLastUnitSpan_relative_filling R C D M X Y)).2
end SerrePositivity.InfinityCategories
