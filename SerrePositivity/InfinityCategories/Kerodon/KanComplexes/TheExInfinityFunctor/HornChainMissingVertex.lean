module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornChainVertices

/-!
# 二重細分の候補像が共通に避ける頂点

概要：一つの面の鎖に含まれる全ての部分鎖の候補頂点は、k と異なる頂点を共通に避ける。
方針：horn 内の面があればその最大の面の欠けた頂点を使い、なければ k 以外の任意の頂点を使う。
規約：Moss 2020 Proposition 21 の Kan 性に向けた候補の horn への包含の証明。
使われ方：二重細分の nerve の各単体の像を horn に制限する。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open PartialOrder

/--
概要：鎖の全ての部分鎖の候補頂点は、k と異なる一つの頂点を共通に避ける。
方針：鎖内の horn に属する面を集め、その最大元に欠けた頂点を使う。
規約：二重細分から k-horn への写像の各単体の像の計算。
使われ方：候補写像の horn への因子化。
-/
theorem hornChainVertex_common_missing (n : ℕ) (hn : 0 < n) (k : Fin (n + 1))
    (M : NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))) :
    ∃ j : Fin (n + 1), j ≠ k ∧
      ∀ C : NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))),
        C ≤ M → hornChainVertex n k C ≠ ULift.up j := by
  classical
  let safe := M.finset.filter (HornFaceSet n k)
  by_cases hsafe : safe.Nonempty
  · let D : NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :=
      { finset := safe
        nonempty := hsafe
        comparable a b := M.comparable ⟨a.val, (Finset.mem_filter.mp a.property).1⟩
          ⟨b.val, (Finset.mem_filter.mp b.property).1⟩ }
    have hD : HornFaceSet n k (finiteChainGreatest D) :=
      (Finset.mem_filter.mp (finiteChainGreatest_mem D)).2
    obtain ⟨j, hj, hjm⟩ := hD
    refine ⟨j, hj, ?_⟩
    intro C hCM he
    obtain ⟨s, hs, hse⟩ := hornChainVertex_exists_face n k C
    by_cases hS : HornFaceSet n k s
    · have hsD : s ∈ D.finset := Finset.mem_filter.mpr ⟨hCM hs, hS⟩
      have hsle : s ≤ finiteChainGreatest D := le_finiteChainGreatest D s hsD
      have hm : finiteChainMaximum s ∈ (finiteChainGreatest D).finset :=
        hsle (Finset.max'_mem s.finset s.nonempty)
      have hc : hornFaceChoice n k s = finiteChainMaximum s := by
        simp only [hornFaceChoice, ite_eq_left hS]
      rw [hc, he] at hse
      exact hjm (hse ▸ hm)
    · have hc : hornFaceChoice n k s = ULift.up k := by
        simp only [hornFaceChoice, ite_eq_right hS]
      rw [hc, he] at hse
      exact hj (congrArg ULift.down hse).symm
  · have hne : ∃ j : Fin (n + 1), j ≠ k := by
      by_cases hk : k = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        intro he
        have hv := congrArg Fin.val he
        simp only [hk, Fin.val_zero] at hv
        omega
      · exact ⟨0, Ne.symm hk⟩
    obtain ⟨j, hj⟩ := hne
    refine ⟨j, hj, ?_⟩
    intro C hCM he
    obtain ⟨s, hs, hse⟩ := hornChainVertex_exists_face n k C
    have hS : ¬ HornFaceSet n k s := by
      intro h
      exact hsafe ⟨s, Finset.mem_filter.mpr ⟨hCM hs, h⟩⟩
    have hc : hornFaceChoice n k s = ULift.up k := by
      simp only [hornFaceChoice, ite_eq_right hS]
    rw [hc, he] at hse
    exact hj (congrArg ULift.down hse).symm

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
