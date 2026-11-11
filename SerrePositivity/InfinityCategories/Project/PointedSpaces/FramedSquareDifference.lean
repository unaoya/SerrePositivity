module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.FramedSquareRelation

/-!
概要：共通下辺を持つ元の二つの正方形から、その右辺の差を元の左辺へ戻す。
方針：上辺と参照左辺の恒等を消し、共通下辺を参照右辺の逆として解く。
規約：差は参照右辺の逆を左から合成する。使われ方：比較 apex 射の符号の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.FramedSquare
end SerrePositivity.KST.Spectra.FramedSquare
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra.FramedSquare

/-- 元の左辺が定値なら、その一単体は元の基点で退化する。 -/
lemma left_constant_edge {X : SSet.{u}} (q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (x : X _⦋0⦌)
    (hl : lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (𝟙 (Δ[1] : SSet.{u})) ≫ q = SSet.const x) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left.map q).edge = (X.σ 0) x := by
  have h := congrArg SSet.yonedaEquiv hl
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left_yoneda, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  have hc := stdSimplex.yonedaEquiv_σ_comp
    (SSet.const x : (Δ[0] : SSet.{u}) ⟶ X) (0 : Fin 1)
  rw [SSet.comp_const, SSet.yonedaEquiv_const] at hc
  exact h.trans hc

variable {X : SSet.{u}} (q r : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (x y : X _⦋0⦌)
    (q00 : q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 0) = x)
    (q10 : q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 0) = y)
    (q01 : q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 1) = x)
    (q11 : q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 1) = x)
    (r00 : r.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 0) = x)
    (r10 : r.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 0) = y)
    (r01 : r.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 1) = x)
    (r11 : r.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 1) = x)

/-- 元の下辺が同じなら、同じ両端表示の辺そのものが等しい。 -/
lemma bottom_eq
    (hb : lift (𝟙 (Δ[1] : SSet.{u}))
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ q =
      lift (𝟙 (Δ[1] : SSet.{u}))
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ r) :
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.bottom q x y q00 q10 = _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.bottom r x y r00 r10 := by
  apply SSet.Edge.ext
  have h := congrArg SSet.yonedaEquiv hb
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.bottom_yoneda, SSet.yonedaEquiv_comp,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h

include r00 r01 in
/-- 元の共通下辺を消去すると、右辺の差は元の左辺の loop の類。 -/
lemma difference
    (hb : lift (𝟙 (Δ[1] : SSet.{u}))
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ q =
      lift (𝟙 (Δ[1] : SSet.{u}))
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ r)
    (qt : lift (𝟙 (Δ[1] : SSet.{u}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ q = SSet.const x)
    (rt : lift (𝟙 (Δ[1] : SSet.{u}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ r = SSet.const x)
    (rl : lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (𝟙 (Δ[1] : SSet.{u})) ≫ r = SSet.const x)
    [IsIso (SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.right r x y r10 r11))] :
    inv (SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.right r x y r10 r11)) ≫
      SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.right q x y q10 q11) =
    SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.left q x q00 q01) := by
  have hq := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.bottom_comp_right q x y q00 q10 q01 q11 (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.top_constant_edge q x qt)
  have hr := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.bottom_comp_right r x y r00 r10 r01 r11 (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.top_constant_edge r x rt)
  have hl : _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.left r x r00 r01 = SSet.Edge.id x := SSet.Edge.ext (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.left_constant_edge r x rl)
  erw [hl, SSet.HomotopyCategory.homMk_id] at hr
  have hi : SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.bottom r x y r00 r10) =
      inv (SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.right r x y r10 r11)) := by
    apply (cancel_mono (SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.right r x y r10 r11))).mp
    rw [hr, IsIso.inv_hom_id]
  rw [← hi, ← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.bottom_eq q r x y q00 q10 r00 r10 hb]
  exact hq

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FramedSquare.bottom_eq := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.bottom_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FramedSquare.difference := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.difference

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FramedSquare.left_constant_edge := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.left_constant_edge
