module

public import SerrePositivity.InfinityCategories.Core.StdSimplexTerminal
public import SerrePositivity.InfinityCategories.Core.ColimitExistenceTransfer
public import SerrePositivity.InfinityCategories.F1B.Cofinality.TerminalPointAnodyne
public import SerrePositivity.InfinityCategories.Core.IdentityCocone
public import SerrePositivity.InfinityCategories.F1.CosliceRestriction

/-!
概要：終頂点を持つ形状、特に一点と標準単体の全図式は余極限を持つ。
方針：一点の恒等余錐を、終頂点包含の right anodyne 性で全体へ延長する。
規約：形状の quasicategory 性は不要で、指定された元の図式を保持する。
使われ方：全有限余極限を生成する有限セル帰納の単体基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 任意の一点図式の余極限は、その点自身である。 -/
lemma hasColimit_pointDiagram {X : SSet.{u}} [Quasicategory X]
    (p : (Δ[0] : SSet.{u}) ⟶ X) : HasColimit p := by
  obtain ⟨x, rfl⟩ := SSet.yonedaEquiv.symm.surjective p
  exact ⟨cosliceIdentityCone x, cosliceIdentityCone_isColimit x⟩

/-- 終頂点を持つ形状の元の図式は余極限を持つ。 -/
lemma hasColimit_of_terminalShapeVertex {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (t : K _⦋0⦌) (ht : IsTerminalVertex t) : HasColimit p := by
  have := cofinalPointInclusion_mono t
  have := sliceUnderRestrict_trivialKanFibration p (SSet.yonedaEquiv.symm t)
    (F1B.terminalPoint_rightAnodyne ht)
  exact (hasColimit_iff_of_trivialRestriction p (SSet.yonedaEquiv.symm t)).mpr
    (hasColimit_pointDiagram _)

/-- 全標準単体の図式は余極限を持つ。 -/
lemma hasColimit_stdSimplex {X : SSet.{u}} [Quasicategory X] (n : ℕ)
    (p : (Δ[n] : SSet.{u}) ⟶ X) : HasColimit p :=
  hasColimit_of_terminalShapeVertex p _ (stdSimplex_last_isTerminalVertex n)

end SerrePositivity.InfinityCategories
