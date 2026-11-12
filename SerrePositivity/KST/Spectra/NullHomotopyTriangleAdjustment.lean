module

public import SerrePositivity.KST.Spectra.NullHomotopyTriangleHorn
public import SerrePositivity.KST.Spectra.NullDifferenceZeroFiller

/-!
概要：移送後との差が零なら、相対ホモトピーを固定して三角形の零ホモトピーを取り替える。
方針：元の三角形、零の差の充填、退化した零ホモトピーを一つ高いホーンへ貼る。
規約：三辺の指定した単体は厳密に保つ。
使われ方：Goerss–Jardine VIII §1。相対ホモトピーの塔の逐次持ち上げの準備。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.NullHomotopyTriangle
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌} {n : ℕ}
  {s t : X.PtSimplex (n + 1) x}
  (R : PtSimplex.RelStruct .const s (Fin.last (n + 1)))
  (A : PtSimplex.RelStruct s t (Fin.last (n + 1)))
  (U V : PtSimplex.RelStruct .const t (Fin.last (n + 1)))
  (φ ψ : (Δ[n + 3] : SSet.{u}) ⟶ X)
  (hφ : ∀ j, stdSimplex.δ j ≫ φ = NullHomotopyTransport.triangleFace R A U j)
  (hψ : ∀ j, stdSimplex.δ j ≫ ψ = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face U V j)

/-- 退化した左辺、零の差、元の三角形を置くホーン。 -/
def adjustmentFace (j : Fin (n + 5)) : (Δ[n + 3] : SSet.{u}) ⟶ X :=
  if j.val = n + 1 then stdSimplex.σ (Fin.last (n + 2)) ≫ R.map else
    if j.val = n + 2 then ψ else if j.val = n + 3 then φ else SSet.const x

omit [KanComplex X] in
include hφ hψ in
/-- 三辺を保って零ホモトピーを交換するホーンは互換。 -/
lemma adjustmentCompatible :
    horn.IsCompatible (i := Fin.last (n + 4)) (fun j _ ↦ adjustmentFace R φ ψ j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val ≠ n + 4 := fun he ↦ hj (Fin.ext he)
  have hk' : k.val ≠ n + 4 := fun he ↦ hk (Fin.ext he)
  have hjb := j.isLt
  have hkb := k.isLt
  have hlt : j.val < k.val := hjk
  simp only [adjustmentFace]
  split_ifs <;> try simp only [hφ, hψ, NullHomotopyTransport.triangleFace,
    NullHomotopyDifference.diagonal_filler_face, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face, comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       try simp only [Fin.val_pred, Fin.coe_castPred] at *
       omega)

include hφ hψ in
/-- 欠ける最後の面は、右の零ホモトピーだけを交換した三角形。 -/
lemma adjustment_output_face (j : Fin (n + 4)) :
    stdSimplex.δ j ≫ stdSimplex.δ (Fin.last (n + 4)) ≫
      (adjustmentCompatible R A U V φ ψ hφ hψ).liftOfKanComplex =
    NullHomotopyTransport.triangleFace R A V j := by
  rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
    (adjustmentCompatible R A U V φ ψ hφ hψ).δ_liftOfKanComplex _ (Fin.castSucc_ne_last j)]
  simp only [adjustmentFace, Fin.val_castSucc]
  split_ifs <;> try simp only [hφ, hψ, NullHomotopyTransport.triangleFace,
    NullHomotopyDifference.diagonal_filler_face, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyDifference.face,
    comp_const]
  all_goals (try split_ifs) <;> first
    | rfl
    | (exfalso
       try simp only [Fin.val_last, Fin.val_pred] at *
       omega)

/-- 移送した零ホモトピーとの差の零性は、指定した三辺の三角形の充填を与える。 -/
theorem exists_triangle_of_zero
    (he : NullHomotopyDifference.difference (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport R A) V = 1) :
    ∃ θ : (Δ[n + 3] : SSet.{u}) ⟶ X,
      ∀ j, stdSimplex.δ j ≫ θ = NullHomotopyTransport.triangleFace R A V j := by
  obtain ⟨ψ, hψ⟩ := NullHomotopyDifference.exists_zero_filler
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport R A) V he
  let φ := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.compatible R A).liftOfKanComplex
  have hφ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.filler_face R A
  exact ⟨stdSimplex.δ (Fin.last (n + 4)) ≫
    (adjustmentCompatible R A _ V φ ψ hφ hψ).liftOfKanComplex,
    adjustment_output_face R A _ V φ ψ hφ hψ⟩

end
end SerrePositivity.KST.Spectra.NullHomotopyTriangle
