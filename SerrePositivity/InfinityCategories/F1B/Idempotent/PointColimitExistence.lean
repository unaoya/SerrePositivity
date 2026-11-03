module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.ColimitExistenceTransfer
public import SerrePositivity.InfinityCategories.Core.IdentityCocone
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.F1.CosliceRestriction
public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialFixedContraction
public import SerrePositivity.InfinityCategories.F1B.Cofinality.TerminalPointAnodyne

/-!
概要：一点図式と終頂点を持つ形状上の任意の図式は余極限を持つ。
方針：一点の恒等余錐を、終頂点への right anodyne 制限の自明 Kan 性で延長する。
規約：図式の全高次単体を保持し、元の形状の Kan 性を要求しない。
使われ方：元の Idem 包含の像の点における左局所余極限の存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 任意の表示の元の一点図式は、恒等余錐を余極限として持つ。 -/
lemma pointDiagram_hasColimit {X : SSet.{u}} [Quasicategory X]
    (p : (Δ[0] : SSet.{u}) ⟶ X) : HasColimit p := by
  obtain ⟨x, rfl⟩ := SSet.yonedaEquiv.symm.surjective p
  exact ⟨cosliceIdentityCone x, cosliceIdentityCone_isColimit x⟩

/-- 指定した終頂点を持つ元の形状上の任意の図式は余極限を持つ。 -/
lemma hasColimit_of_terminal_vertex {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (t : K _⦋0⦌) (ht : IsTerminalVertex t) : HasColimit p := by
  have := cofinalPointInclusion_mono t
  have := sliceUnderRestrict_trivialKanFibration p
    (SSet.yonedaEquiv.symm t) (SerrePositivity.InfinityCategories.F1B.terminalPoint_rightAnodyne ht)
  exact (hasColimit_iff_of_trivialRestriction p (SSet.yonedaEquiv.symm t)).mpr
    (pointDiagram_hasColimit _)

end SerrePositivity.InfinityCategories.F2.Idempotent
