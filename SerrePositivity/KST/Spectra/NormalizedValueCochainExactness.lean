module

public import SerrePositivity.KST.Spectra.NormalizedValueCochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
概要：正規化 cohomology の消滅を cocycle の原像の存在へ移す。
方針：加法群の複体の完全性を、微分の核の元が像に属する条件で読む。
規約：通常の正規化微分の値で述べる。塔への適用は別に行う。
使われ方：Goerss–Jardine VIII §1。骨格の障害を補正する cochain の選択。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra.NormalizedValueCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 零 cohomology 次数の cocycle は通常の正規化微分の像。 -/
theorem exists_primitive_of_isZero (K : SSet.{u}) (M : AddCommGrpCat.{u}) (n : ℕ)
    (hH : IsZero ((complex K M).homology (n + 1)))
    (z : K.nonDegenerate (n + 1) → M) (hz : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M (n + 1) z = 0) :
    ∃ a : K.nonDegenerate n → M, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M n a = z := by
  have he := ((complex K M).exactAt_iff_isZero_homology (n + 1)).2 hH
  have he' := ((complex K M).exactAt_iff' (i := n) (j := n + 1) (k := n + 2)
    (by simp) (by simp)).1 he
  have hs := (ShortComplex.ab_exact_iff ((complex K M).sc' n (n + 1) (n + 2))).1 he'
  have hd (i : ℕ) : (complex K M).d i (i + 1) =
      AddCommGrpCat.ofHom (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M i) :=
    CochainComplex.of_d (fun n ↦ AddCommGrpCat.of (K.nonDegenerate n → M))
      (fun n ↦ AddCommGrpCat.ofHom (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M n)) i
  have hz' : (complex K M).d (n + 1) (n + 2) z = 0 := by
    rw [hd (n + 1)]
    exact hz
  obtain ⟨a, ha⟩ := hs z hz'
  refine ⟨a, ?_⟩
  change (complex K M).d n (n + 1) a = z at ha
  rw [hd n] at ha
  exact ha

end
end SerrePositivity.KST.Spectra.NormalizedValueCochains
