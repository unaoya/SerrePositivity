module

public import SerrePositivity.KST.Spectra.SphericalFiberLift
public import SerrePositivity.KST.Spectra.FibrationMultiplication

/-!
概要：fiber に入る最後の二面を、連結射の最後の一面へまとめる。
方針：逆元の積と二面の差の積を、底の退化単体に沿う相対ホーンへ貼る。
規約：連結射は最後の面を取る規約。球面的な面の次数は一以上。
使われ方：Goerss–Jardine I §8。相対交代境界関係の終端。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SphericalFiberLift

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : SSet.{u}} {p : E ⟶ B} {e : E _⦋0⦌} {n : ℕ}
  {s : B.PtSimplex (n + 2) (p.app _ e)}
  {a : Fin (n + 3) → (KanFiber p (p.app _ e)).PtSimplex (n + 1) (fiberPoint p e)}
  {ia c : (KanFiber p (p.app _ e)).PtSimplex (n + 1) (fiberPoint p e)}

/-- 概要：終端の相対ホーンの既知の面。
方針：元の単体、逆元の積、二面の差の積を順に置く。
規約：欠ける面は n+1、積の添字は n。
使われ方：Goerss–Jardine I §8。最後の二面を連結射へまとめる。 -/
def terminalFace
    (hi : PtSimplex.MulStruct ia (a (Fin.last (n + 1)).castSucc) .const (Fin.last n))
    (hc : PtSimplex.MulStruct ia (a (Fin.last (n + 1)).succ) c (Fin.last n))
    (T : SphericalFiberLift p e s a) (j : Fin (n + 4)) : (Δ[n + 2] : SSet.{u}) ⟶ E :=
  if j.val = n then T.map else
  if j.val = n + 2 then hi.map ≫ fiberι p (p.app _ e) else
  if j.val = n + 3 then hc.map ≫ fiberι p (p.app _ e) else SSet.const e

/-- fiber の先頭の定数面は全空間でも定数。 -/
lemma lowerMap (hlower : ∀ j, j.val < n + 1 → a j = .const)
    (j : Fin (n + 3)) (hj : j.val < n + 1) :
    (a j).map ≫ fiberι p (p.app _ e) = SSet.const e := by
  rw [hlower j hj]
  simp only [RelativeMorphism.const_map, const_comp, fiberι_point]

set_option maxHeartbeats 1200000 in
-- 三つの指定面と退化面の全ての交わりを有限分岐で計算する。
/-- 概要：終端の相対ホーンの面は互換である。
方針：三つの非定数面の交わりで積の面と元の面を比較する。
規約：元の単体の最初の n+1 面は定数。
使われ方：Goerss–Jardine I §8。相対 Kan 充填の条件。 -/
lemma terminalCompatible
    (hi : PtSimplex.MulStruct ia (a (Fin.last (n + 1)).castSucc) .const (Fin.last n))
    (hc : PtSimplex.MulStruct ia (a (Fin.last (n + 1)).succ) c (Fin.last n))
    (T : SphericalFiberLift p e s a)
    (hlower : ∀ j, j.val < n + 1 → a j = .const) :
    horn.IsCompatible (i := (Fin.last (n + 1)).castSucc.castSucc)
      (fun j _ ↦ terminalFace hi hc T j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 1 := by intro he; exact hj (Fin.ext he)
  have hk' : k.val ≠ n + 1 := by intro he; exact hk (Fin.ext he)
  have hjb : j.val < n + 4 := j.isLt
  have hkb : k.val < n + 4 := k.isLt
  have hlt : j.val < k.val := hjk
  simp only [terminalFace]
  split_ifs <;> try simp only [← Category.assoc] <;>
    try simp only [SimplexFaces.mul_face, RelativeMorphism.const_map, comp_const]
  all_goals (try split_ifs) <;> try simp only [const_comp, fiberι_point]
  all_goals try rw [T.face_eq]
  all_goals first
    | rfl
    | (apply congrArg (fun t ↦ (a t).map ≫ fiberι p (p.app _ e)); apply Fin.ext
       simp only [Fin.val_last, Fin.val_castSucc, Fin.val_succ,
         Fin.coe_castPred, Fin.val_pred] at *
       omega)
    | (apply lowerMap hlower
       simp only [Fin.val_pred, Fin.val_last, Fin.val_castSucc, Fin.val_succ] at *
       omega)
    | (symm; apply lowerMap hlower
       simp only [Fin.coe_castPred, Fin.val_last, Fin.val_castSucc,
         Fin.val_succ] at *
       omega)
    | (exfalso
       simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.val_succ,
         Fin.coe_castPred, Fin.val_pred, Fin.lt_def] at *
       omega)

/-- 概要：終端ホーンの射影は底の指定した退化単体の境界である。
方針：fiber を通る二面の射影は定数、元の単体だけは底の単体。
規約：欠ける面は n+1。
使われ方：Goerss–Jardine I §8。底を固定する相対充填。 -/
lemma terminalFace_comp
    (hi : PtSimplex.MulStruct ia (a (Fin.last (n + 1)).castSucc) .const (Fin.last n))
    (hc : PtSimplex.MulStruct ia (a (Fin.last (n + 1)).succ) c (Fin.last n))
    (T : SphericalFiberLift p e s a) (j : Fin (n + 4))
    (hj : j ≠ (Fin.last (n + 1)).castSucc.castSucc) :
    terminalFace hi hc T j ≫ p =
      stdSimplex.δ j ≫ stdSimplex.σ (Fin.last n).castSucc.castSucc ≫ s.map := by
  rw [SimplexFaces.degenerate_face]
  have hj' : j.val ≠ n + 1 := by intro he; exact hj (Fin.ext he)
  simp only [terminalFace, Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> try (exfalso; omega)
  all_goals simp only [Category.assoc, fiberι_comp, comp_const, const_comp, T.map_comp]

/-- 概要：終端ホーンの欠ける面は最後の面以外で定数となる。
方針：二面交換公式で既知の面へ移し、積の三面を計算する。
規約：最後の面は差を表す c の全空間への包含。
使われ方：Goerss–Jardine I §8。連結射の境界代表の構成。 -/
lemma terminalOutput_face
    (hi : PtSimplex.MulStruct ia (a (Fin.last (n + 1)).castSucc) .const (Fin.last n))
    (hc : PtSimplex.MulStruct ia (a (Fin.last (n + 1)).succ) c (Fin.last n))
    (T : SphericalFiberLift p e s a)
    (hlower : ∀ j, j.val < n + 1 → a j = .const)
    (φ : (Δ[n + 3] : SSet.{u}) ⟶ E)
    (hφ : ∀ j, j ≠ (Fin.last (n + 1)).castSucc.castSucc →
      stdSimplex.δ j ≫ φ = terminalFace hi hc T j) (j : Fin (n + 3)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last (n + 1)).castSucc.castSucc ≫ φ =
      if j = Fin.last (n + 2) then c.map ≫ fiberι p (p.app _ e) else SSet.const e := by
  have hjb : j.val < n + 3 := j.isLt
  let q : Fin (n + 3) := (Fin.last n).castSucc.castSucc
  have hq : (Fin.last (n + 1)).castSucc.castSucc = q.succ := by apply Fin.ext; rfl
  by_cases hj : j ≤ q
  · rw [hq, stdSimplex.δ_comp_δ_assoc hj, hφ _ (by
      intro he; have := congrArg Fin.val he
      simp only [Fin.val_castSucc, Fin.val_last] at this
      have := hj
      simp only [Fin.le_def, q, Fin.val_castSucc, Fin.val_last] at this
      omega)]
    simp only [terminalFace]
    split_ifs <;> try simp only [← Category.assoc] <;>
      try simp only [SimplexFaces.mul_face, RelativeMorphism.const_map]
    all_goals (try split_ifs) <;> try simp only [const_comp, fiberι_point]
    all_goals try rw [T.face_eq]
    all_goals first
      | rfl
      | (apply lowerMap hlower
         simp only [Fin.val_last, Fin.val_castSucc, Fin.val_succ, q] at *
         omega)
      | (exfalso
         simp only [Fin.ext_iff, Fin.le_def, Fin.val_last, Fin.val_castSucc,
           Fin.val_succ, q] at *
         omega)
  · have hm : (Fin.last (n + 1)).castSucc ≤ j := by
      simp only [Fin.le_def, q, Fin.val_last, Fin.val_castSucc] at *
      omega
    rw [← stdSimplex.δ_comp_δ_assoc hm, hφ _ (by
      intro he; have he' := congrArg Fin.val he
      simp only [Fin.val_succ, Fin.val_last, Fin.val_castSucc] at he'
      have hjv := hm
      simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hjv
      omega)]
    simp only [terminalFace]
    split_ifs <;> try simp only [← Category.assoc] <;>
      try simp only [SimplexFaces.mul_face, RelativeMorphism.const_map]
    all_goals (try split_ifs) <;> try simp only [const_comp, fiberι_point]
    all_goals try rw [T.face_eq]
    all_goals first
      | rfl
      | (exfalso
         simp only [Fin.ext_iff, Fin.le_def, Fin.val_last, Fin.val_castSucc,
           Fin.val_succ, q] at *
         first | omega | simp_all only)

/-- 概要：最後の二面を正規化した、同じ底の単体の BoundaryLift。
方針：互換な終端ホーンを底の退化に沿って持ち上げ、欠ける面を取る。
規約：最後の面は c、他の面は定数。
使われ方：Goerss–Jardine I §8。連結射を二面の差で計算する。 -/
def terminalLift [Fibration p]
    (hi : PtSimplex.MulStruct ia (a (Fin.last (n + 1)).castSucc) .const (Fin.last n))
    (hc : PtSimplex.MulStruct ia (a (Fin.last (n + 1)).succ) c (Fin.last n))
    (T : SphericalFiberLift p e s a)
    (hlower : ∀ j, j.val < n + 1 → a j = .const) : BoundaryLift p e s := by
  let hex := (terminalCompatible hi hc T hlower).exists_lift p
    (stdSimplex.σ (Fin.last n).castSucc.castSucc ≫ s.map)
    (terminalFace_comp hi hc T)
  let φ := Classical.choose hex
  have hφ := (Classical.choose_spec hex).1
  have hcomp := (Classical.choose_spec hex).2
  refine ⟨stdSimplex.δ (Fin.last (n + 1)).castSucc.castSucc ≫ φ, ?_, ?_⟩
  · rw [Category.assoc, hcomp, SimplexFaces.degenerate_face]
    exact ite_eq_left (Or.inr (by apply Fin.ext; rfl))
  · intro j hj
    rw [terminalOutput_face hi hc T hlower φ hφ j, ite_eq_right hj]

/-- 概要：正規化した持ち上げの最後の面は指定した差の単体。
方針：fiber の包含で比較し、終端ホーンの最後の面を計算する。
規約：代表そのものの厳密な等式。
使われ方：Goerss–Jardine I §8。連結射の選択独立性への入力。 -/
lemma terminalLift_boundary [Fibration p]
    (hi : PtSimplex.MulStruct ia (a (Fin.last (n + 1)).castSucc) .const (Fin.last n))
    (hc : PtSimplex.MulStruct ia (a (Fin.last (n + 1)).succ) c (Fin.last n))
    (T : SphericalFiberLift p e s a)
    (hlower : ∀ j, j.val < n + 1 → a j = .const) :
    (terminalLift hi hc T hlower).boundary = c := by
  ext : 1
  apply fiber_hom_ext p (p.app _ e)
  rw [BoundaryLift.boundary_ι]
  exact (terminalOutput_face hi hc T hlower _
    (Classical.choose_spec ((terminalCompatible hi hc T hlower).exists_lift p _
      (terminalFace_comp hi hc T))).1 (Fin.last (n + 2))).trans (ite_eq_left rfl)

end
end SerrePositivity.KST.Spectra.SphericalFiberLift
