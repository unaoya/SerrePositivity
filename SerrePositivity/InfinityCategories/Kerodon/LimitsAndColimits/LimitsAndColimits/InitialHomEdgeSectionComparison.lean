module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomEdgeCylinder
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.RelativeEdgeCosliceSectionComparison

/-!
概要：元の Hom 比較で選んだ全辺族を、同じ終点と底の普遍相対切断の像へ照合する。
方針：データに保持した終点・底の式を使い、両方を固定した円柱を得る。
規約：元の中間持ち上げを選び直さない。使われ方：前置写像と元の HL・HR の照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {E B T : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q]
  (c : E _⦋0⦌) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c) (e : (Δ[1] : SSet.{u}) ⟶ E)
  (he : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm c) (y : B _⦋0⦌)
  (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e))
  (ha : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) ≫ q = SSet.const y)
  (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (e ≫ q))
  (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q =
    b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (e ≫ q) (stdSimplex.δ (0 : Fin 2)))
  (hb : b = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSection (e ≫ q))
local notation "D" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialHomEdgeCylinder q c hc e he y a ha b h

include hb in
/-- 元の全辺族と普遍相対切断の像は、同じ終点と底を全時刻で保って結べる。 -/
lemma exists_initialHomEdgeSectionComparison :
    ∃ H : SSet.Homotopy (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection e q) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomEdgeCylinder.fullFamily D),
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) = fst T Δ[1] ≫ a ∧
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp e q = fst T Δ[1] ≫ b := by
  obtain ⟨H, ht, hB⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_relativeEdgeCosliceSection_comparison e q a (D).fullFamily
    (D).full_target ((D).full_base.trans hb)
  exact ⟨H, ht, by simpa only [hb, Category.assoc] using hB⟩

/-- 同じ元の全辺族を終点に持つ、保持した終点・底固定の実際の比較円柱。 -/
def initialHomEdgeSectionComparison :
    SSet.Homotopy (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection e q) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomEdgeCylinder.fullFamily D) :=
  (exists_initialHomEdgeSectionComparison q c hc e he y a ha b h hb).choose

/-- 元の終点側の全族を、比較円柱の全時刻で厳密に固定する。 -/
lemma initialHomEdgeSectionComparison_target :
    (initialHomEdgeSectionComparison q c hc e he y a ha b h hb).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) = fst T Δ[1] ≫ a :=
  (exists_initialHomEdgeSectionComparison q c hc e he y a ha b h hb).choose_spec.1

/-- 底も元の同じ全合成族を全時刻で厳密に固定する。 -/
lemma initialHomEdgeSectionComparison_base :
    (initialHomEdgeSectionComparison q c hc e he y a ha b h hb).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp e q =
      fst T Δ[1] ≫ b :=
  (exists_initialHomEdgeSectionComparison q c hc e he y a ha b h hb).choose_spec.2

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
