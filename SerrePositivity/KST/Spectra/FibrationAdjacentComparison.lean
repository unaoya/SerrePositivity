module

public import SerrePositivity.KST.Spectra.RelativePathBoundaryLift
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SphericalBoundaryReduction

/-!
概要：同じ底の単体を持つ境界定数の持ち上げと定数ホーンの持ち上げを比較する。
方針：二つの持ち上げを隣接する二面へ置き、底の退化単体に沿って最後の面を充填する。
規約：V は面 n、U は面 n+1、欠ける面は n+2。向きを入れ替えない。
使われ方：Goerss–Jardine I §8。loop と連結射の逆符号の幾何的比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.AdjacentLiftComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : SSet.{u}} {p : E ⟶ B} {e : E _⦋0⦌} {n : ℕ}
  {s : B.PtSimplex (n + 1) (p.app _ e)}
  (U : E.PtSimplex (n + 1) e) (V : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s)

/-- 概要：二つの持ち上げを最後の面の手前へ置く比較ホーンの面。
方針：残る面は全空間の基点で定数とする。
規約：面 n が V、面 n+1 が U。
使われ方：Goerss–Jardine I §8。連結射の交換比較。 -/
def face (j : Fin (n + 3)) : (Δ[n + 1] : SSet.{u}) ⟶ E :=
  if j.val = n then V.map else if j.val = n + 1 then U.map else SSet.const e

/-- 概要：比較ホーンの面は互換である。
方針：U の全ての面と V の最後以外の面が定数であることを使う。
規約：最後の面だけを欠く外側ホーン。
使われ方：Goerss–Jardine I §8。相対 Kan 充填の前提。 -/
lemma compatible : horn.IsCompatible (i := Fin.last (n + 2)) (fun j _ ↦ face U V j) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  have hj' : j.val < n + 2 := by
    have := j.isLt
    have : j.val ≠ n + 2 := fun he ↦ hj (Fin.ext he)
    omega
  have hk' : k.val < n + 2 := by
    have := k.isLt
    have : k.val ≠ n + 2 := fun he ↦ hk (Fin.ext he)
    omega
  have hjk' : j.val < k.val := hjk
  have hkp : k ≠ 0 := by
    intro he; subst k; exact (Fin.not_lt_zero j hjk)
  have hVk := V.face_eq (k.pred hkp) (by
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_pred, Fin.val_last] at this
    omega)
  simp only [face]
  split_ifs <;> simp only [hVk, PtSimplex.δ_map, comp_const]
  all_goals first
    | rfl
    | (rw [V.face_eq (j.castPred hj) (by
         intro he; have := congrArg Fin.val he
         simp only [Fin.coe_castPred, Fin.val_last] at this
         omega)])

/-- 概要：比較ホーンは底の退化単体の境界に沿う。
方針：二つの持ち上げの射影と境界定数単体の退化の面を比較する。
規約：底の退化は σ_(n)。
使われ方：Goerss–Jardine I §8。底を固定する相対充填。 -/
lemma face_comp (hU : U.map ≫ p = s.map) (j : Fin (n + 3))
    (_hj : j ≠ Fin.last (n + 2)) :
    face U V j ≫ p = stdSimplex.δ j ≫ stdSimplex.σ (Fin.last n).castSucc ≫ s.map := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face]
  simp only [face, Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> try (exfalso; omega)
  all_goals simp only [V.map_comp, hU, const_comp]

/-- 概要：比較ホーンを実際に相対充填する。
方針：互換性と射影の式に Kan fibration のホーン持ち上げを適用する。
規約：最後の面を後で fiber 内の path として読む。
使われ方：Goerss–Jardine I §8。二方向の連結射の共通比較単体。 -/
theorem exists_lift [Fibration p] (hU : U.map ≫ p = s.map) :
    ∃ φ : (Δ[n + 2] : SSet.{u}) ⟶ E,
      (∀ j, j ≠ Fin.last (n + 2) → stdSimplex.δ j ≫ φ = face U V j) ∧
        φ ≫ p = stdSimplex.σ (Fin.last n).castSucc ≫ s.map :=
  (compatible U V).exists_lift p _ (face_comp U V hU)

/-- 概要：比較単体の最後の面の射影は基点に定数。
方針：底の退化の最後の面を計算する。
規約：最後の面の次数は n+1。
使われ方：Goerss–Jardine I §8。比較の出力を fiber へ入れる。 -/
lemma last_comp (φ : (Δ[n + 2] : SSet.{u}) ⟶ E)
    (hφ : φ ≫ p = stdSimplex.σ (Fin.last n).castSucc ≫ s.map) :
    (stdSimplex.δ (Fin.last (n + 2)) ≫ φ) ≫ p = SSet.const (p.app _ e) := by
  rw [Category.assoc, hφ, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SimplexFaces.degenerate_face]
  exact ite_eq_right (by simp [Fin.ext_iff])

/-- 概要：比較単体の最後の面を fiber へ入れる。
方針：射影が定数という式を pullback の持ち上げにする。
規約：これはまだ境界定数単体ではなく、一つの非定数な面を持つ。
使われ方：Goerss–Jardine I §8。fiber 内の path の族。 -/
def output (φ : (Δ[n + 2] : SSet.{u}) ⟶ E)
    (hφ : φ ≫ p = stdSimplex.σ (Fin.last n).castSucc ≫ s.map) :
    (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p (p.app _ e) (stdSimplex.δ (Fin.last (n + 2)) ≫ φ) (last_comp φ hφ)

/-- 概要：出力を fiber から全空間へ戻すと比較単体の最後の面。
方針：pullback の第一射影を計算する。
規約：代表の厳密な等式。
使われ方：Goerss–Jardine I §8。出力の面と終点の検査。 -/
@[reassoc (attr := simp)]
lemma output_ι (φ : (Δ[n + 2] : SSet.{u}) ⟶ E)
    (hφ : φ ≫ p = stdSimplex.σ (Fin.last n).castSucc ≫ s.map) :
    output φ hφ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) = stdSimplex.δ (Fin.last (n + 2)) ≫ φ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι ..

/-- 概要：比較出力の非定数面は最後から二番目にだけ現れる。
方針：二面交換で既知の面へ移し、V の最後の面と U の定数面を計算する。
規約：非定数面は V の境界代表そのもの。
使われ方：Goerss–Jardine I §8。連結射の交換の逆符号を生む面の位置。 -/
lemma output_face (φ : (Δ[n + 2] : SSet.{u}) ⟶ E)
    (hφ : φ ≫ p = stdSimplex.σ (Fin.last n).castSucc ≫ s.map)
    (hface : ∀ j, j ≠ Fin.last (n + 2) → stdSimplex.δ j ≫ φ = face U V j)
    (j : Fin (n + 2)) :
    stdSimplex.δ j ≫ output φ hφ =
      if j.val = n then V.boundary.map else SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ e)
  rw [Category.assoc, output_ι,
    stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
    hface _ (Fin.castSucc_ne_last j)]
  simp only [face, Fin.val_castSucc]
  split_ifs <;> try rw [PtSimplex.δ_map]
  · exact V.boundary_ι.symm
  all_goals simp only [comp_const, const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point]

end
end SerrePositivity.KST.Spectra.AdjacentLiftComparison
