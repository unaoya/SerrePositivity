module

public import Mathlib.Topology.Sets.Opens

/-!
概要：KST §5、Stacks Lemma 31.35.5 の互いに交わらない開被覆の各部分の閉性。
方針：一つの部分の補集合を他の開部分の和で表す。
規約：この位相的補題には被覆の有限性は不要。
使われ方：階数を分離したチャートから延長した中心の支持を、そのチャートの像の内側に保つ。
-/

@[expose] public section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：互いに交わらない開集合の被覆の各部分は閉集合でもある。
方針：補集合を添字が異なる開集合の和として計算する。
規約：KST §5、Stacks Lemma 31.35.5、空の添字集合も許す。
使われ方：有限チャートの局所中心を正確に貼り合わせるための閉じた像の条件。
-/
theorem isClosed_of_disjoint_open_cover {X ι : Type*} [TopologicalSpace X]
    (U : ι → TopologicalSpace.Opens X) (hU : (⨆ i, U i) = ⊤)
    (hd : Pairwise (fun i j => Disjoint (U i) (U j))) (i : ι) :
    IsClosed (U i : Set X) := by
  apply isOpen_compl_iff.mp
  have hc : (U i : Set X)ᶜ = ⋃ j, ⋃ (_ : j ≠ i), (U j : Set X) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion]
    constructor
    · intro hi
      have hx : x ∈ ⨆ j, U j := by rw [hU]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      refine ⟨j, ?_, hj⟩
      rintro rfl
      exact hi hj
    · rintro ⟨j, hji, hj⟩ hi
      exact (disjoint_iff_inf_le.mp (hd hji)) ⟨hj, hi⟩
  rw [hc]
  exact isOpen_iUnion (fun j => isOpen_iUnion (fun _ => (U j).isOpen))

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
