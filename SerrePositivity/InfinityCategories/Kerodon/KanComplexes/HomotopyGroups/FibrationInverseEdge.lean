module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationBoundary

/-!
概要：底の逆元の三角形を fibration に沿って持ち上げる。
方針：元の辺の持ち上げと定数辺をホーンへ置く。
規約：連結射の代表となる辺とは逆向きの辺を構成する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。二つの三角形の交換と逆元の比較。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：底の左逆元を表す辺は、全空間で基点から元の持ち上げの始点への辺として持ち上がる。
方針：逆元の三角形の零面に元の持ち上げ、一面に定数辺を置いて二面を充填する。
規約：元の持ち上げは始点から基点へ向かう。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。pullback の二因子の交換の成分の計算。 -/
theorem exists_inverse_edge {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (e : E _⦋0⦌) {s t : B.PtSimplex 1 (p.app _ e)} (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s)
    (m : PtSimplex.MulStruct t s .const (0 : Fin 1)) :
    ∃ K : (Δ[1] : SSet.{u}) ⟶ E,
      K ≫ p = t.map ∧
      stdSimplex.δ (0 : Fin 2) ≫ K = stdSimplex.δ (1 : Fin 2) ≫ L.map ∧
      stdSimplex.δ (1 : Fin 2) ≫ K = SSet.const e := by
  let α (j : Fin 3) (_ : j ≠ 2) : (Δ[1] : SSet.{u}) ⟶ E :=
    if j = 0 then L.map else SSet.const e
  have hα : horn.IsCompatible (i := (2 : Fin 3)) α := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    have hjv : j.val ≠ 2 := fun he => hj (Fin.ext he)
    have hkv : k.val ≠ 2 := fun he => hk (Fin.ext he)
    have hjkv : j.val < k.val := hjk
    have hj0 : j = 0 := by apply Fin.ext; change j.val = 0; omega
    have hk1 : k = 1 := by apply Fin.ext; change k.val = 1; omega
    subst j
    subst k
    simpa [α] using L.face_eq (0 : Fin 2) (by decide)
  have hp : ∀ j hj, α j hj ≫ p = stdSimplex.δ j ≫ m.map := by
    intro j hj
    fin_cases j
    · change L.map ≫ p = stdSimplex.δ (0 : Fin 3) ≫ m.map
      exact L.map_comp.trans m.δ_castSucc_castSucc_map.symm
    · change SSet.const e ≫ p = stdSimplex.δ (1 : Fin 3) ≫ m.map
      rw [SSet.const_comp]
      exact m.δ_succ_castSucc_map.symm
    · exact (hj rfl).elim
  obtain ⟨φ, hφ, hcomp⟩ := hα.exists_lift p m.map hp
  refine ⟨stdSimplex.δ (2 : Fin 3) ≫ φ, ?_, ?_, ?_⟩
  · rw [Category.assoc, hcomp]
    exact m.δ_succ_succ_map
  · have hδ : stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) =
        stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) :=
      stdSimplex.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
    rw [← Category.assoc, hδ, Category.assoc, hφ _ (by decide)]
    rfl
  · have hδ : stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) =
        stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) :=
      stdSimplex.δ_comp_δ (i := (1 : Fin 2)) (j := (1 : Fin 2)) (by decide)
    rw [← Category.assoc, hδ, Category.assoc, hφ _ (by decide)]
    exact SSet.comp_const _ _

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
