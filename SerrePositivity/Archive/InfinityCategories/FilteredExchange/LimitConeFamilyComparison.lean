module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamilyFunctor
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeTerminalFamilyHomotopy

/-!
概要：元の錐族から部分極限の族への比較を、元の底の図式を固定して構成する。
方針：各点の極限錐の相対終点境界充填を族へ移し、固定底の円柱を取る。
規約：元の二族を端点とする全円柱。使われ方：有限形状の貼り合わせの部分極限比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の極限錐の族の各頂点は、元の形状制限の相対終点境界充填を持つ。 -/
lemma terminalBoundaryLifting_of_limitConeFamily {B K X : SSet.{u}} [Quasicategory X]
    (q : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X)
    (hq : ∀ b : B _⦋0⦌, IsLimitCone (functorVertexCone (q.app (Opposite.op ⦋0⦌) b)))
    (b : B _⦋0⦌) :
    TerminalBoundaryLifting (coneRestriction K X) (q.app (Opposite.op ⦋0⦌) b) := by
  have h := terminalBoundaryLifting_coneRestriction_of_isLimitCone _ (hq b)
  have he : functorVertex (functorVertexCone (q.app (Opposite.op ⦋0⦌) b)).val =
      q.app (Opposite.op ⦋0⦌) b := (functorVertexEquiv _ _).apply_symm_apply _
  rwa [he] at h

/-- 元の錐族から同じ図式の極限錐族へ、底を全時刻で固定する比較円柱が存在。 -/
lemma exists_limitConeFamilyComparison {B K X : SSet.{u}} [Quasicategory X]
    (f q : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X)
    (hfq : f ≫ coneRestriction K X = q ≫ coneRestriction K X)
    (hq : ∀ b : B _⦋0⦌, IsLimitCone (functorVertexCone (q.app (Opposite.op ⦋0⦌) b))) :
    ∃ H : SSet.Homotopy f q,
      H.h ≫ coneRestriction K X = fst B (Δ[1] : SSet.{u}) ≫ (f ≫ coneRestriction K X) :=
  exists_homotopy_to_relativeTerminal_family (coneRestriction K X) f q hfq
    (terminalBoundaryLifting_of_limitConeFamily q hq)

end SerrePositivity.InfinityCategories.F2
