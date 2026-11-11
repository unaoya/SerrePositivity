module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertexSupport

/-! # 立方体の出力一座標の有限 max 表示
概要：出力一座標を定数一、または入力座標の有限集合の max として表す。
方針：零頂点で定数一を分離し、一座標頂点で有限集合を回収して表示の単射性を示す。
規約：none は定数一、some の空集合は定数零。使われ方：cubical 射の具体的な正規形。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction

/-- 出力一座標の定数一、または有限 max の表示。 -/
abbrev CubeJoinTerm (n : ℕ) := Option (Finset (Fin n))

/-- 元の立方体の頂点における有限 max 表示の値。 -/
def cubeJoinTermEval {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinTerm n) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) : Bool :=
  match s with
  | none => true
  | some t => t.sup x

/-- 零頂点での値は、元の表示が定数一であるかを検出する。 -/
lemma cubeJoinTermEval_bot {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinTerm n) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval s ⊥ = s.isNone := by
  cases s with
  | none => rfl
  | some t => exact Finset.sup_bot t

/-- 有限集合における一座標頂点の max は、その座標の所属を検出する。 -/
lemma cubeVertexAtom_sup_finset {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    s.sup (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i) = decide (i ∈ s) := by
  apply Bool.eq_iff_iff.mpr
  change s.sup (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i) = ⊤ ↔ decide (i ∈ s) = ⊤
  rw [Finset.sup_eq_top_iff]
  simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom]

/-- 出力一座標の有限 max 表示は、その元の全頂点での関数から一意に回収される。 -/
lemma cubeJoinTermEval_injective (n : ℕ) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval (n := n)) := by
  intro s t h
  cases s with
  | none =>
    cases t with
    | none => rfl
    | some t =>
      have hzero : (true : Bool) = false := by
        simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval_bot, Option.isNone_none, Option.isNone_some] using
          congrFun h (⊥ : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n)
      cases hzero
  | some s =>
    cases t with
    | none =>
      have hzero : (false : Bool) = true := by
        simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval_bot, Option.isNone_none, Option.isNone_some] using
          congrFun h (⊥ : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n)
      cases hzero
    | some t =>
      have hst : s = t := by
        apply Finset.ext
        intro i
        have hi := congrFun h (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i)
        simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom_sup_finset] at hi
        simpa using (Iff.of_eq (congrArg (fun b : Bool => b = true) hi))
      exact congrArg Option.some hst

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinTerm (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeJoinTerm := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinTerm

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinTermEval := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinTermEval_bot := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval_bot

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinTermEval_injective := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval_injective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeVertexAtom_sup_finset := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom_sup_finset

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinTermEval.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinTermEval.eq_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval.eq_2

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinTermEval.match_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval.match_1
