module

public import SerrePositivity.KST.LocalizingInvariants.VerdierQuotientConeRefinement
public import SerrePositivity.InfinityCategories.Core.FixedDiagramHomotopy

/-!
概要：指定商錐への全比較を、元の有限境界を全時刻で固定する実経路として回収する。
方針：同じ slice 同型を固定図式の fiber へ写し、その中の可逆辺を実現する。
規約：境界上の比較を同型類だけで固定せず、全円柱の厳密な等式で保持する。
使われ方：c5 の尾部と元の図式を貼る際の、共有境界上の定値比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 同じ slice 同型を、元の全境界を全時刻で固定する可逆ホモトピーとして表す。 -/
lemma exists_coneRelativeComparison {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c d : JoinCone p) (e : VertexIso (X := sliceOver p) c d) :
    ∃ H : SSet.Homotopy c.val d.val,
      (joinInr (Δ[0] : SSet.{u}) K ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        fst K Δ[1] ≫ p ∧
      ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated := by
  have ef := VertexIso.map e (sliceConeFamilyMap p)
  change VertexIso (X := coneFamily p)
    ((sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) c)
    ((sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) d) at ef
  rw [sliceConeFamilyMap_app_zero, sliceConeFamilyMap_app_zero] at ef
  exact exists_relative_homotopy_of_fixedDiagram_vertexIso
    (joinInr (Δ[0] : SSet.{u}) K) p c.val d.val c.property d.property ef

/-- 任意の指定有限商錐を、元の境界を全時刻で固定する同じ全比較付きで回収する。 -/
lemma exists_verdierQuotientConeRelativeComparison {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    {K : SSet.{u}} [K.Finite] (p : K ⟶ B.obj) (t : JoinCone (p ≫ q.hom)) :
    ∃ (c : JoinCone p) (H : SSet.Homotopy (c.val ≫ q.hom) t.val),
      (joinInr (Δ[0] : SSet.{u}) K ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        fst K Δ[1] ≫ (p ≫ q.hom) ∧
      ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge H x).toTruncated := by
  obtain ⟨c, ⟨e⟩⟩ := exists_verdierQuotientConeIsoRefinement h p t
  obtain ⟨H, hH, hi⟩ := exists_coneRelativeComparison (mapJoinCone q.hom c) t e
  exact ⟨c, H, hH, hi⟩

end SerrePositivity.KST.LocalizingInvariants
