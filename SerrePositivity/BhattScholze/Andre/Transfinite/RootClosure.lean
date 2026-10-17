module

public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Polynomial.Lifts

/-! # 超限反復の終段における絶対整閉性

BS Thm 7.14（著者版 p.61）の超限反復に必要な根の移送を扱う。
極限環の完備性・perfectoid性・完全忠実平坦性はこのファイルでは主張しない。
-/

@[expose] public noncomputable section

open Polynomial
universe u
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)

/-- ## 概要
各段の正次数モニック多項式が後の段で根を持てば、有向余極限は絶対整閉である。
BS Thm 7.14（著者版 p.61）の超限反復の最後の根の存在を実現する。

## 方針
Mathlib の有限係数の降下からモニックかつ同次数の多項式を選び、後の段の根を余極限へ送る。

## 規約
遷移写像の単射性、環の非零性、添字の非可算共終性はこの代数的結論には不要。
正の次数条件を必須とし、定数多項式 `1` の根を要求しない。

## 使われ方
完備な超限塔を別途構成した後、その終段の絶対整閉性を証明する。
-/
theorem isAbsolutelyIntegrallyClosed_directLimit_of_eventual_roots
    (hroot : ∀ i (P : Polynomial (R i)), P.Monic → 0 < P.natDegree →
    ∃ (j : ι) (hij : i ≤ j) (x : R j), P.eval₂ (f i j hij) x = 0) :
    IsAbsolutelyIntegrallyClosed (Ring.DirectLimit R (fun i j h ↦ f i j h)) := by
  classical
  intro P hP hdeg
  obtain ⟨i, Q, hQ⟩ := Ring.DirectLimit.Polynomial.exists_of P
  obtain ⟨Q', hmap, hdegree, hmonic⟩ :=
    lifts_and_natDegree_eq_and_monic (mem_lifts _ |>.mpr ⟨Q, hQ⟩) hP
  obtain ⟨j, hij, x, hx⟩ := hroot i Q' hmonic (hdegree ▸ hdeg)
  refine ⟨Ring.DirectLimit.of R (fun i j h ↦ f i j h) j x, ?_⟩
  rw [IsRoot, ← hmap, eval_map]
  have hcompat : (Ring.DirectLimit.of R (fun i j h ↦ f i j h) j).comp (f i j hij) =
      Ring.DirectLimit.of R (fun i j h ↦ f i j h) i := by
    ext a
    exact Ring.DirectLimit.of_f hij a
  rw [← hcompat, ← hom_eval₂, hx, map_zero]
end SerrePositivity.BhattScholze.Andre.Transfinite
