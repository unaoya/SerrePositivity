module

public import SerrePositivity.InfinityCategories.F2.PointConeDegeneracy
public import SerrePositivity.InfinityCategories.F1B.KanSliceIdentityTerminal
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightFibrationInvertibleReflection
public import SerrePositivity.InfinityCategories.Core.TerminalTransport

/-!
概要：一点図式の元の錐と恒等錐の間の比較は、底で元の脚そのもの。
方針：元の脚の終点を重ねた退化三角形を slice の辺にする。
規約：元の比較辺を保持。使われ方：指定脚の可逆性による一点極限錐の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の一点錐から恒等錐への指定された比較辺。 -/
def pointConeIdentityComparison {X : SSet.{u}} (x : X _⦋0⦌)
    (c : JoinCone (SSet.yonedaEquiv.symm x)) :
    (sliceOver (SSet.yonedaEquiv.symm x)).Edge c (sliceIdentityCone x) where
  edge := ⟨pointConeDegeneracy ≫ c.val, by
    change joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ (pointConeDegeneracy ≫ c.val) = _
    rw [← Category.assoc, pointConeDegeneracy_inr, c.property]⟩
  src_eq := by
    apply Subtype.ext
    change joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 Δ[0]) ≫
      (pointConeDegeneracy ≫ c.val) = c.val
    rw [← Category.assoc, pointConeDegeneracy_face_one, Category.id_comp]
  tgt_eq := by
    apply Subtype.ext
    change joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 Δ[0]) ≫
      (pointConeDegeneracy ≫ c.val) = SSet.const x
    rw [← Category.assoc, pointConeDegeneracy_face_zero, SSet.const_comp]
    congr 1
    have h := congrArg SSet.yonedaEquiv c.property
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
    exact h

/-- 指定比較辺の底への像は、元の一点錐の脚の標準辺の表示。 -/
lemma pointConeIdentityComparison_projection_edge {X : SSet.{u}} (x : X _⦋0⦌)
    (c : JoinCone (SSet.yonedaEquiv.symm x)) :
    ((pointConeIdentityComparison x c).map
      (sliceOverProjection (SSet.yonedaEquiv.symm x))).edge = (sliceOverVertexEdge x c).edge := by
  change SSet.yonedaEquiv (joinInl Δ[1] Δ[0] ≫ (pointConeDegeneracy ≫ c.val)) = _
  rw [← Category.assoc, pointConeDegeneracy_inl]
  rfl

/-- 元の一点錐が極限であることと、元の指定脚が可逆なことは同値。 -/
lemma isLimitCone_point_iff_invertible {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) (c : JoinCone (SSet.yonedaEquiv.symm x)) :
    IsLimitCone c ↔ IsInvertibleEdge (sliceOverVertexEdge x c) := by
  let e := pointConeIdentityComparison x c
  have hd := F1B.kanSliceIdentityCone_isTerminalVertex x
  constructor
  · intro hc
    have he : IsInvertibleEdge e.toTruncated :=
      isIso_of_isTerminal hc.isTerminalHo hd.isTerminalHo _
    exact (isInvertibleEdge_congr (pointConeIdentityComparison_projection_edge x c)).mp
      (he.map (sliceOverProjection (SSet.yonedaEquiv.symm x)))
  · intro hc
    have hp : IsInvertibleEdge (e.map (sliceOverProjection (SSet.yonedaEquiv.symm x))) :=
      (isInvertibleEdge_congr (pointConeIdentityComparison_projection_edge x c)).mpr hc
    have he := HomotopyLimits.rightFibration_reflects_isInvertibleEdge
      (sliceOverProjection (SSet.yonedaEquiv.symm x)) e hp
    have : IsIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) := he
    exact hd.of_vertexIso (asIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)).symm

/-- 一点図式の任意の表示でも、元の標準脚の可逆性が極限性を判定する。 -/
lemma isLimitCone_point_iff_edge {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ IsInvertibleEdge (edgeOfSimplex
      (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ c.val))) := by
  obtain ⟨x, rfl⟩ := SSet.yonedaEquiv.symm.surjective p
  exact (isLimitCone_point_iff_invertible x c).trans
    (isInvertibleEdge_congr (rfl : (sliceOverVertexEdge x c).edge = _))

end SerrePositivity.InfinityCategories.F2
