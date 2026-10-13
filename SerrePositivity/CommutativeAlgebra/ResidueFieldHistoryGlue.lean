module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldDiagramGlue
public import SerrePositivity.CommutativeAlgebra.ResidueFieldHistory

/-! # 先行する閉図式から開図式を構成する

対角段を共有する環として採用し、終域までの図式から写像を取り出す。
制限一致による段の等式に沿って源の構造を移し、旧図式全体の保持を証明する。
-/

@[expose] public section
namespace SerrePositivity
open IsLocalRing
universe u
variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]
variable [LinearOrder K]
variable (i : K)
variable (p : ∀ j, j < i → LocalAlgebraDiagram B K {k : K // k ≤ j})
variable (hc : ∀ j k (hj : j < i) (hk : k < i) (hjk : j < k),
  residueFieldHistoryRestrict j k hjk (p k hk) = p j hj)

include hc

/-- 先行履歴の開初期部分への貼り合わせ。下方集合の共通構成を使う。 -/
def residueFieldOpenGlue : LocalAlgebraDiagram B K {j : K // j < i} :=
  localAlgebraLowerGlue (fun j ↦ j < i) p hc

omit [IsScalarTower B (ResidueField B) K] in
/-- 開図式は先行履歴の全法則を満たす。 -/
theorem residueFieldOpenGlue_spec
    (hp : ∀ j h, IsResidueFieldDiagram (p j h)
      (fun k ↦ residueGeneratorAfter (ResidueField B) K k.val)) :
    IsResidueFieldDiagram (residueFieldOpenGlue i p hc)
      (fun j ↦ residueGeneratorAfter (ResidueField B) K j.val) :=
  residueFieldDiagramLowerGlue_spec (fun j ↦ j < i) p hc
    (fun h hl ↦ lt_of_le_of_lt h hl) (residueGeneratorAfter (ResidueField B) K) hp

omit [IsLocalRing B] [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K] in
/-- 各先行履歴へ制限すると、構造と写像を含め元の図式全体に等しい。 -/
theorem residueFieldOpenGlue_restrict (l : K) (hl : l < i) :
    (residueFieldOpenGlue i p hc).reindex
      (fun j : {j : K // j ≤ l} ↦ ⟨j.val, lt_of_le_of_lt j.property hl⟩)
      (fun _ _ h ↦ h) = p l hl :=
  localAlgebraLowerGlue_restrict (fun j ↦ j < i) p hc
    (fun h hl ↦ lt_of_le_of_lt h hl) l hl

omit hc in
/-- 先行履歴の貼り合わせを実構成で供給し、全段の両立した閉図式を得る。 -/
theorem exists_coherent_residueFieldHistories
    (wf : WellFounded ((· < ·) : K → K → Prop)) :
    ∃ s : ∀ i, LocalAlgebraDiagram B K {j : K // j ≤ i},
      ∀ i, IsResidueFieldDiagram (s i)
        (fun j ↦ residueGeneratorAfter (ResidueField B) K j.val) ∧
        ∀ j (h : j < i), residueFieldHistoryRestrict j i h (s i) = s j := by
  apply exists_coherent_residueFieldHistories_of_open_gluing wf
  intro i p hp hc
  exact ⟨residueFieldOpenGlue i p hc, residueFieldOpenGlue_spec i p hc hp,
    residueFieldOpenGlue_restrict i p hc⟩

end SerrePositivity
