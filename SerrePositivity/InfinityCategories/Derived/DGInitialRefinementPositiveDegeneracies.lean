module
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementInitialMaps

/-! # 正番号退化と同じ閉始点細分の厳密可換性

概要：始点以外の基本退化は零を固定し正番号を非零へ送り、閉始点細分と可換。
方針：有限順序写像の値を照合し、非単射を含む一般制限定理へ渡す。
規約：零番号退化を含むとは主張しない。使われ方：実錐の標準退化の保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

omit [CommRing A] [DGCategory A D] in
/-- 基本退化の順序写像は、零頂点を零へ送る。 -/
lemma dgDegeneracy_zero {n : ℕ} (j : Fin (n + 1)) : j.predAboveOrderHom 0 = 0 :=
  Fin.predAbove_right_zero (i := j)

omit [CommRing A] [DGCategory A D] in
/-- 正番号基本退化の順序写像は、正番号頂点を零へ潰さない。 -/
lemma dgPositiveDegeneracy_ne_zero {n : ℕ} (j : Fin (n + 1)) (hj : j ≠ 0)
    (i : Fin (n + 2)) (hi : i ≠ 0) : j.predAboveOrderHom i ≠ 0 := by
  intro he
  change j.predAbove i = 0 at he
  have hjv : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj
  have hiv : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi
  unfold Fin.predAbove at he
  split_ifs at he with h
  · have hv := congrArg Fin.val he
    simp only [Fin.val_pred, Fin.val_zero] at hv
    have hl : j.val < i.val := h
    omega
  · have hv := congrArg Fin.val he
    simp only [Fin.coe_castPred, Fin.val_zero] at hv
    omega

/-- 正番号基本退化と、任意次元の同じ実単体の閉始点細分は厳密に可換。 -/
lemma dgSimplexInitialRefinement_degeneracy_positive {n : ℕ} (t : Simplex A D n)
    (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0))
    (j : Fin (n + 1)) (hj : j ≠ 0) :
    (dgNerve A D).σ j (dgSimplexInitialRefinement A D t q s) =
      dgSimplexInitialRefinement A D ((dgNerve A D).σ j t) q
        (dgClosedTargetTransport A D s (congrArg t.obj (dgDegeneracy_zero j).symm)) :=
  dgSimplexInitialRefinement_pullback_initial A D t q s j.predAboveOrderHom
    (dgDegeneracy_zero j) (fun i hi => dgPositiveDegeneracy_ne_zero j hj i hi)

end SerrePositivity.InfinityCategories
