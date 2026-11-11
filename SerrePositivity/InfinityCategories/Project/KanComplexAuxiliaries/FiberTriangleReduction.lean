module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SphericalFiberNormalization

/-!
概要：fiber の三つの辺を持つ三角形の先頭の面を相対 Kan 充填で消す。
方針：先頭辺の逆元の積、元の三角形、残りの積を四面体の三面へ置く。
規約：底の二単体を固定し、辺の順序を保持する。
使われ方：Goerss–Jardine I §8、VIII §1。次数一の交代微分の境界公式。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.FiberTriangle
end SerrePositivity.KST.Spectra.FiberTriangle
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction
open _root_.SerrePositivity.KST.Spectra.FiberTriangle

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : SSet.{u}} {p : E ⟶ B} {e : E _⦋0⦌}
  {s : B.PtSimplex 2 (p.app _ e)}
  {a : Fin 3 → (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)}
  {ia b : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)}

/-- 先頭辺の逆元と残りの辺の積による簡約ホーンの面。 -/
def face (hi : PtSimplex.MulStruct ia (a 0) .const 0)
    (hb : PtSimplex.MulStruct b ia (a 2) 0)
    (T : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SphericalFiberLift p e s a) (j : Fin 4) : (Δ[2] : SSet.{u}) ⟶ E :=
  if j = 0 then hi.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) else
  if j = 1 then T.map else hb.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)

/-- 相対簡約ホーンの既知の三面は互換。 -/
lemma compatible (hi : PtSimplex.MulStruct ia (a 0) .const 0)
    (hb : PtSimplex.MulStruct b ia (a 2) 0) (T : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SphericalFiberLift p e s a) :
    horn.IsCompatible (i := (2 : Fin 4)) (fun j _ ↦ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face hi hb T j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hlt : j.val < k.val := hjk
  fin_cases j <;> fin_cases k <;>
    simp_all [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face, Fin.ext_iff, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.mul_face,
      T.face_eq]

/-- 既知の三面の射影は、底の二単体の指定した退化の境界。 -/
lemma face_comp (hi : PtSimplex.MulStruct ia (a 0) .const 0)
    (hb : PtSimplex.MulStruct b ia (a 2) 0) (T : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SphericalFiberLift p e s a)
    (j : Fin 4) (hj : j ≠ 2) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face hi hb T j ≫ p = stdSimplex.δ j ≫ stdSimplex.σ (1 : Fin 3) ≫ s.map := by
  fin_cases j <;> simp_all [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face, Fin.ext_iff, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp,
    T.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face]

/-- 先頭の面を定数とし、最後の面を積の代表に置き換えた辺族。 -/
def reduced (a : Fin 3 → (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e))
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)) (j : Fin 3) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)).PtSimplex 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) :=
  if j = 0 then .const else if j = 2 then b else a j

/-- 簡約ホーンの欠ける面の三辺を厳密に計算する。 -/
lemma output_face (hi : PtSimplex.MulStruct ia (a 0) .const 0)
    (hb : PtSimplex.MulStruct b ia (a 2) 0) (T : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SphericalFiberLift p e s a)
    (φ : (Δ[3] : SSet.{u}) ⟶ E)
    (hφ : ∀ j : Fin 4, j ≠ 2 → stdSimplex.δ j ≫ φ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face hi hb T j) (j : Fin 3) :
    stdSimplex.δ j ≫ stdSimplex.δ (2 : Fin 4) ≫ φ =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced a b j).map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) := by
  fin_cases j
  · change stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) ≫ φ = _
    erw [stdSimplex.δ_comp_δ_assoc (show (0 : Fin 3) ≤ 1 by decide), hφ 0 (by decide)]
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced, Fin.ext_iff, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.mul_face]
  · change stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) ≫ φ = _
    erw [stdSimplex.δ_comp_δ_assoc (show (1 : Fin 3) ≤ 1 by decide), hφ 1 (by decide)]
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced, Fin.ext_iff, T.face_eq]
  · change stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) ≫ φ = _
    erw [← stdSimplex.δ_comp_δ_assoc (show (2 : Fin 3) ≤ 2 by decide), hφ 3 (by decide)]
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced, Fin.ext_iff, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.mul_face]

/-- 底の二単体を変更せずに先頭の辺を消去する相対 Kan 充填。 -/
def reduce [Fibration p] (hi : PtSimplex.MulStruct ia (a 0) .const 0)
    (hb : PtSimplex.MulStruct b ia (a 2) 0) (T : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SphericalFiberLift p e s a) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SphericalFiberLift p e s (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced a b) := by
  let hex := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.compatible hi hb T).exists_lift p (stdSimplex.σ (1 : Fin 3) ≫ s.map)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face_comp hi hb T)
  let φ := Classical.choose hex
  have hφ := (Classical.choose_spec hex).1
  have hp := (Classical.choose_spec hex).2
  refine ⟨stdSimplex.δ (2 : Fin 4) ≫ φ, ?_, ?_⟩
  · rw [Category.assoc, hp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face]
    simp [Fin.ext_iff]
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.output_face hi hb T φ hφ

end
end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.compatible := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.compatible

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.face := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.face_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.output_face := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.output_face

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduce (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.reduce := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduce

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.reduced := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.face._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.face._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.face._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.face._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.face.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.face.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.reduce._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduce._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.reduce._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduce._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.reduce._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduce._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.reduce._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduce._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.reduce._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduce._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.reduce._simp_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduce._simp_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FiberTriangle.reduced.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberTriangleReduction.reduced.eq_1
