module
public import SerrePositivity.KST.SConstruction.SimplicialDiagramDiagonalEnrichedFunctor

/-! # 対角実現作用の元の各段での評価
概要：図式全体への全入力族の対角作用を、同じ次数の元の射影作用で回収する。
方針：curry の自然性と対角作用の評価式を使う。
規約：入力を頂点に制限しない。使われ方：全零方向の作用との可換性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 全入力族の元の対角作用は、各次数で同じ元の内部 Hom 射影の作用。 -/
lemma simplicialSSetDiagramDiagonal_parameter_app {X Y : SimplicialSSetDiagram.{u}}
    {P : SSet.{u}} (a : P ⟶ (X ⟶[SSet.{u}] Y)) (n : SimplexCategoryᵒᵖ)
    (x : (simplicialSSetDiagramDiagonal X).obj n) (p : P.obj n) :
    (uncurry (a ≫ simplicialSSetDiagramDiagonalEnrichedFunctor.map X Y)).app n (x, p) =
      (uncurry (a ≫ simplicialSSetDiagramProjection X Y n)).app n (x, p) := by
  change (uncurry (a ≫ curry (simplicialSSetDiagramDiagonalAction X Y))).app n (x, p) = _
  rw [uncurry_natural_left, uncurry_curry, uncurry_natural_left]
  rfl

end SerrePositivity.KST.SConstruction
