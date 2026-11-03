module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.LimitConeFamilyComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeTerminalFamilyTriangle

/-!
概要：同じ部分図式の極限錐族へ向かう指定比較円柱の三角形を構成する。
方針：終点族の極限性を相対終点境界充填へ移し、元の三辺の族を充填する。
規約：底の図式は全二単体で固定。使われ方：貼り合わせの共通対角辺の保持。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の極限錐族へ向かう三つの指定比較は、底を固定する三角形の族を持つ。 -/
lemma limitConeFamilyComparisonTriangle {B K X : SSet.{u}} [Quasicategory X]
    (a : B ⟶ (ihom K).obj X)
    {f g h : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X}
    (hh : ∀ b : B _⦋0⦌, IsLimitCone (functorVertexCone (h.app (Opposite.op ⦋0⦌) b)))
    (l : SSet.Homotopy f g) (r : SSet.Homotopy g h) (d : SSet.Homotopy f h)
    (hl : l.h ≫ coneRestriction K X = fst B (Δ[1] : SSet.{u}) ≫ a)
    (hr : r.h ≫ coneRestriction K X = fst B (Δ[1] : SSet.{u}) ≫ a)
    (hd : d.h ≫ coneRestriction K X = fst B (Δ[1] : SSet.{u}) ≫ a) :
    Nonempty {T : FunctorCompositionTriangle l r d //
      T.diagram ≫ (ihom B).map (coneRestriction K X) = SSet.const (functorVertex a)} :=
  relativeTerminalFamilyTriangle (coneRestriction K X) a
    (terminalBoundaryLifting_of_limitConeFamily h hh) l r d hl hr hd

end SerrePositivity.InfinityCategories.F2
