module

public import SerrePositivity.KST.LocalizingInvariants.PullbackRelativeExtension

/-!
概要：最終外ホーンの外にある単体の最後の頂点は、標準単体の末尾の二点のいずれか。
方針：最後から二番目の頂点が値域に入ることと、頂点列の単調性を使う。
規約：単体の次数は任意。使われ方：二つの普遍正方形だけによる相対延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma finalHorn_not_mem_last_value (m d : ℕ) (s : (Δ[m + 2] : SSet.{u}) _⦋d⦌)
    (hs : s ∉ (horn (m + 2) (Fin.last (m + 2))).obj (Opposite.op ⦋d⦌)) :
    s (Fin.last d) = (Fin.last (m + 1)).castSucc ∨ s (Fin.last d) = Fin.last (m + 2) := by
  have hj : (Fin.last (m + 1)).castSucc ≠ Fin.last (m + 2) := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at h'
    omega
  have hr : (Fin.last (m + 1)).castSucc ∈ Set.range s := by
    by_contra h
    exact hs ((mem_horn_iff_notMem_range s (Fin.last (m + 2))).mpr ⟨_, hj, h⟩)
  obtain ⟨k, hk⟩ := hr
  have hle := stdSimplex.monotone_apply s (Fin.le_last k)
  have hle' : (Fin.last (m + 1)).castSucc ≤ s (Fin.last d) :=
    le_trans (le_of_eq hk.symm) hle
  change m + 1 ≤ (s (Fin.last d)).val at hle'
  by_cases h : s (Fin.last d) = Fin.last (m + 2)
  · exact Or.inr h
  · left
    apply Fin.ext
    have hlt := (s (Fin.last d)).isLt
    have hn : (s (Fin.last d)).val ≠ m + 2 := fun h' => h (Fin.ext h')
    change (s (Fin.last d)).val = m + 1
    omega

lemma simplexLastVertex_stdSimplex {m d : ℕ} (s : (Δ[m] : SSet.{u}) _⦋d⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s = stdSimplex.obj₀Equiv.symm (s (Fin.last d)) := by
  apply stdSimplex.ext
  intro i
  rfl

lemma finalHorn_missing_last_vertex (m d : ℕ) (s : (Δ[m + 2] : SSet.{u}) _⦋d⦌)
    (hs : s ∉ (horn (m + 2) (Fin.last (m + 2))).obj (Opposite.op ⦋d⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s = stdSimplex.obj₀Equiv.symm ((Fin.last (m + 1)).castSucc) ∨
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s = stdSimplex.obj₀Equiv.symm (Fin.last (m + 2)) := by
  rw [simplexLastVertex_stdSimplex]
  exact (finalHorn_not_mem_last_value m d s hs).imp
    (congrArg stdSimplex.obj₀Equiv.symm) (congrArg stdSimplex.obj₀Equiv.symm)

end SerrePositivity.KST.LocalizingInvariants
