module

public import SerrePositivity.CategoryTheory.WellFoundedHistory
public import SerrePositivity.CommutativeAlgebra.ResidueFieldDiagramExtension

/-! # 両立する閉初期部分の履歴

整礎再帰を実際の一段延長へ接続する。
この制御APIでは、先行閉図式を開初期部分へ貼り合わせる構成を明示的な仮定にする。
ResidueFieldHistoryGlueでその実構成を供給する。
この条件付き定理だけでは一般体拡大の存在を証明したことにはならない。
-/

@[expose] public section
namespace SerrePositivity
open IsLocalRing
universe u
variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]
variable [LinearOrder K]

/-- 閉初期部分の履歴を、より小さい閉初期部分へ制限する。 -/
def residueFieldHistoryRestrict (j i : K) (h : j < i)
    (D : LocalAlgebraDiagram B K {k : K // k ≤ i}) :
    LocalAlgebraDiagram B K {k : K // k ≤ j} :=
  D.reindex (fun k ↦ ⟨k.val, k.property.trans h.le⟩) (fun _ _ hk ↦ hk)

/-- 開初期部分を構成する貼り合わせがあれば、全段で両立する検証済み閉図式を得る。
一段延長の存在と旧段の保持は入力にせず、証明済みの実構成を適用する。 -/
theorem exists_coherent_residueFieldHistories_of_open_gluing
    (wf : WellFounded ((· < ·) : K → K → Prop))
    (glueOpen : ∀ i
      (p : ∀ j, j < i → LocalAlgebraDiagram B K {k : K // k ≤ j}),
      (∀ j h, IsResidueFieldDiagram (p j h)
        (fun k ↦ residueGeneratorAfter (ResidueField B) K k.val)) →
      (∀ j k (hj : j < i) (hk : k < i) (hjk : j < k),
        residueFieldHistoryRestrict j k hjk (p k hk) = p j hj) →
      ∃ D : LocalAlgebraDiagram B K {j : K // j < i},
        IsResidueFieldDiagram D (fun j ↦ residueGeneratorAfter (ResidueField B) K j.val) ∧
        ∀ j (hj : j < i), D.reindex
          (fun k : {k : K // k ≤ j} ↦ ⟨k.val, lt_of_le_of_lt k.property hj⟩)
          (fun _ _ h ↦ h) = p j hj) :
    ∃ s : ∀ i, LocalAlgebraDiagram B K {j : K // j ≤ i},
      ∀ i, IsResidueFieldDiagram (s i)
        (fun j ↦ residueGeneratorAfter (ResidueField B) K j.val) ∧
        ∀ j (h : j < i), residueFieldHistoryRestrict j i h (s i) = s j := by
  apply exists_coherent_wellFounded_history wf
    (fun i ↦ LocalAlgebraDiagram B K {j : K // j ≤ i}) residueFieldHistoryRestrict
    (fun _ D ↦ IsResidueFieldDiagram D
      (fun j ↦ residueGeneratorAfter (ResidueField B) K j.val))
  intro i p hp hc
  obtain ⟨D, hD, hrestrict⟩ := glueOpen i p hp hc
  refine ⟨residueFieldExtendDiagram i D hD, residueFieldExtendDiagram_spec i D hD, ?_⟩
  intro j hj
  rw [← hrestrict j hj]
  have heq := congrArg
    (fun E : LocalAlgebraDiagram B K {k : K // k < i} ↦ E.reindex
      (fun k : {k : K // k ≤ j} ↦ ⟨k.val, lt_of_le_of_lt k.property hj⟩)
      (fun _ _ h ↦ h)) (residueFieldExtendDiagram_restrict i D hD)
  exact (LocalAlgebraDiagram.reindex_comp (residueFieldExtendDiagram i D hD)
    (fun k : {k : K // k < i} ↦ ⟨k.val, k.property.le⟩) (fun _ _ h ↦ h)
    (fun k : {k : K // k ≤ j} ↦ ⟨k.val, lt_of_le_of_lt k.property hj⟩)
    (fun _ _ h ↦ h)).symm.trans heq

end SerrePositivity
