module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.NoetherianSpace

/-!
概要：Noether 位相空間上で構成可能性を台の閉部分に沿って判定する。
方針：既約閉部分ごとに非空開部分を取り、その補集合に Noether 帰納を適用する。
規約：始域と台はいずれも Noether 空間とする。
使われ方：切断を通るファイバー成分の構成可能性。
-/

@[expose] public section

namespace SerrePositivity.AlgebraicGeometry

open Set TopologicalSpace Topology

/--
概要：台の各既約閉部分の非空開部分上で開集合と一致する部分集合は構成可能。
方針：既約の場合は開部分の補集合に帰納し、一般の場合は既約閉部分の有限和に分ける。
規約：各開部分は台と始域の開集合で指定する。
使われ方：切断を通るファイバー成分の構成可能性。
-/
theorem isConstructible_of_open_over_irreducible_strata
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NoetherianSpace X] [NoetherianSpace Y] {f : X → Y} (hf : Continuous f) (s : Set X)
    (hstrata : ∀ C : Closeds Y, IsIrreducible (C : Set Y) →
      ∃ (V : Opens Y) (W : Opens X), ((C : Set Y) ∩ V).Nonempty ∧
        s ∩ f ⁻¹' ((C : Set Y) ∩ V) = (W : Set X) ∩ f ⁻¹' ((C : Set Y) ∩ V)) :
    IsConstructible s := by
  have openConstructible (U : Opens X) : IsConstructible (U : Set X) :=
    (NoetherianSpace.isCompact _).isConstructible U.isOpen
  have closedConstructible {D : Set X} (hD : IsClosed D) : IsConstructible D := by
    simpa only [Opens.coe_mk, compl_compl] using (openConstructible ⟨Dᶜ, hD.isOpen_compl⟩).compl
  suffices h : ∀ C : Closeds Y, IsConstructible (s ∩ f ⁻¹' (C : Set Y)) by
    simpa using h ⊤
  intro C
  refine wellFounded_lt.induction (C := fun D : Closeds Y =>
    IsConstructible (s ∩ f ⁻¹' (D : Set Y))) C ?_
  clear C
  intro C ih
  by_cases hC : IsIrreducible (C : Set Y)
  · obtain ⟨V, W, hV, hW⟩ := hstrata C hC
    let D : Closeds Y := ⟨(C : Set Y) ∩ (V : Set Y)ᶜ, C.isClosed.inter V.isOpen.isClosed_compl⟩
    have hDC : D < C := by
      refine lt_of_le_not_ge inter_subset_left ?_
      obtain ⟨y, hyC, hyV⟩ := hV
      exact fun h => (h hyC).2 hyV
    have hOpen : IsConstructible (s ∩ f ⁻¹' ((C : Set Y) ∩ V)) := by
      rw [hW, preimage_inter]
      exact (openConstructible W).inter <|
        (closedConstructible (C.isClosed.preimage hf)).inter
          (openConstructible ⟨_, V.isOpen.preimage hf⟩)
    have hSplit : s ∩ f ⁻¹' (C : Set Y) =
        (s ∩ f ⁻¹' ((C : Set Y) ∩ V)) ∪ (s ∩ f ⁻¹' (D : Set Y)) := by
      ext x
      by_cases hx : f x ∈ (V : Set Y) <;> simp [D, hx]
    rw [hSplit]
    exact hOpen.union (ih D hDC)
  · obtain ⟨S, hSfin, hSirr, hCover⟩ :=
      NoetherianSpace.exists_finite_set_closeds_irreducible C
    have hlt : ∀ D ∈ S, D < C := by
      intro D hD
      refine lt_of_le_of_ne ?_ ?_
      · rw [hCover]
        exact le_sSup hD
      · exact fun e => hC (e ▸ hSirr D hD)
    have hUnion : s ∩ f ⁻¹' (C : Set Y) =
        ⋃ D ∈ S, s ∩ f ⁻¹' (D : Set Y) := by
      have hClosed : IsClosed (⋃ D ∈ S, (D : Set Y)) :=
        hSfin.isClosed_biUnion fun D _ => D.isClosed
      rw [hCover, Closeds.coe_sSup, sUnion_image, hClosed.closure_eq]
      simp only [preimage_iUnion, inter_iUnion]
    rw [hUnion]
    exact IsConstructible.biUnion hSfin fun D hD => ih D (hlt D hD)

end SerrePositivity.AlgebraicGeometry
