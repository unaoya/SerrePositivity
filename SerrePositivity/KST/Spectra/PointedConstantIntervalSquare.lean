module

public import SerrePositivity.KST.Spectra.PointedIntervalNaturality
public import SerrePositivity.KST.Spectra.SquareBoundaryFamilies

/-!
概要：同じ実区間を構造方向に一定とする正方形と、その両端境界。
方針：元の辺へ射影し、端点の実際の pointFamily を評価する。
規約：新たな充填なし。使われ方：全 Hom 由来の実評価区間の厳密構造正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
variable {A E : PointedSimplicialSet.{u}} {f g : A ⟶ E}
  (P : VerticalPath (PointedObject.toPoint E) f g)

/-- 同じ辺を構造方向に一定として保持する実正方形。 -/
def constantSquare : SSet.Homotopy P.path P.path where
  h := fst (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ P.path
  h₀ := by
    simp only [← Category.assoc, SSet.ι₀_fst, Category.id_comp]
    rfl
  h₁ := by
    simp only [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
    rfl
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

private lemma terminal_pointFamily (q : A ⟶ E) :
    stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u}) ≫ pointFamily q =
      SSet.const (familyVertex q) := by
  have ht : stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u}) =
      SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [ht, SSet.const_comp, ← SSet.yonedaEquiv_comp, Category.id_comp]
  rfl

/-- 左辺は元の始点で全区間が一定。 -/
lemma constantSquare_start :
    SquareAdjustment.leftSide ≫ P.constantSquare.h = SSet.const (familyVertex f) := by
  have hl : SquareAdjustment.leftSide.{u} ≫ fst (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) =
      stdSimplex.isTerminalObj₀.from _ ≫ stdSimplex.δ (1 : Fin 2) := rfl
  change SquareAdjustment.leftSide ≫ (fst _ _ ≫ P.path) = _
  rw [← Category.assoc, hl, Category.assoc, P.zero]
  exact terminal_pointFamily f

/-- 右辺も元の終点で全区間が一定。 -/
lemma constantSquare_finish :
    SquareAdjustment.rightSide ≫ P.constantSquare.h = SSet.const (familyVertex g) := by
  have hr : SquareAdjustment.rightSide.{u} ≫ fst (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) =
      stdSimplex.isTerminalObj₀.from _ ≫ stdSimplex.δ (0 : Fin 2) := rfl
  change SquareAdjustment.rightSide ≫ (fst _ _ ≫ P.path) = _
  rw [← Category.assoc, hr, Category.assoc, P.one]
  exact terminal_pointFamily g

end SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
