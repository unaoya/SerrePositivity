module

public import Mathlib.Logic.Function.Basic
public import SerrePositivity.CommutativeAlgebra.ResidueFieldExtension.Diagram
public import SerrePositivity.CommutativeAlgebra.ResidueFieldExtension.Step
public import SerrePositivity.CommutativeAlgebra.ResidueFieldExtension.WellFoundedHistory

/-! # 剰余体拡大の図式の超限の貼り合わせ

## 概要

閉初期部分の一段延長（`ResidueFieldExtension/Step`）を局所代数の図式（`LocalAlgebraDiagram`）として述べ、
整礎再帰（`CategoryTheory.WellFoundedHistory`）で、すべての添字について制限が一致する閉初期部分の
図式の族（両立する履歴）を構成する（`exists_coherent_residueFieldHistories`）。

## 方針

図式としての一段延長（`ResidueFieldDiagramExtension`）、下方に閉じた添字集合での法則の保存
（`ResidueFieldDiagramGlue`）、履歴の再帰（`ResidueFieldHistory`）を順に示し、先行する閉図式を開初期部分へ
貼り合わせる構成（`residueFieldOpenGlue`）で再帰の仮定を満たす。

## 規約

図式の移送は `ResidueFieldExtension/Diagram` の構造を保つ等式で行う。関数版の図式
（`ResidueFieldExtension/AlgebraSystem`）との一本化と、Mathlib の `WellOrderInductionData` による書き直しは、
Mathlib に出すときの計画（mathlib-upstream の G8）。

## 使われ方

最終定理（`ResidueFieldExtension/General`）。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section DiagramExtension

open IsLocalRing
variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]

/-- 指定中間体を像に持つ平坦局所代数図式の検証述語。 -/
def IsResidueFieldDiagram {ι : Type u} [Preorder ι]
    (D : LocalAlgebraDiagram B K ι) (F : ι → IntermediateField (ResidueField B) K) : Prop :=
  DirectedSystem D.obj (D.map · · ·) ∧
  (∀ j k h, IsLocalHom (D.map j k h).toRingHom) ∧
  (∀ j k h x, D.target k (D.map j k h x) = D.target j x) ∧
  (∀ j, Module.Flat B (D.obj j)) ∧
  (∀ j, (maximalIdeal B).map (algebraMap B (D.obj j)) = maximalIdeal (D.obj j)) ∧
  (∀ j, Set.range (D.target j) = (F j : Set K))

variable [LinearOrder K] (i : K)
variable (D : LocalAlgebraDiagram B K {j : K // j < i})

/-- 一段のデータを、旧段の構造も含む閉初期部分の図式として格納する。 -/
def residueFieldDiagramOfStep (d : ResidueFieldClosedStepData (B := B) i D.obj) :
    LocalAlgebraDiagram B K {j : K // j ≤ i} where
  obj := algebraInitialSegmentObj i D.obj d.carrier
  map := algebraInitialSegmentMap i D.obj d.carrier D.map d.incoming
  target := algebraInitialSegmentTarget i D.obj d.carrier D.target d.target

omit [IsScalarTower B (ResidueField B) K] in
/-- 閉延長の検証から、図式の全段の検証へ移す。 -/
theorem residueFieldDiagramOfStep_spec
    (d : ResidueFieldClosedStepData (B := B) i D.obj)
    (hd : IsResidueFieldClosedExtension i D.obj D.map D.target d.carrier d.incoming d.target) :
    IsResidueFieldDiagram (residueFieldDiagramOfStep i D d)
      (fun j ↦ residueGeneratorAfter (ResidueField B) K j.val) := by
  rcases hd with ⟨_, _, _, _, _, _, _, _, hds, hlocal, htarget, hflat, hmax, hrange⟩
  exact ⟨hds, hlocal, htarget, hflat, hmax, hrange⟩

omit [IsScalarTower B (ResidueField B) K] [IsLocalRing B] [Algebra (ResidueField B) K] in
/-- 延長を旧添字へ制限すると、環・代数の構造と写像を含め元の図式に一致する。 -/
theorem residueFieldDiagramOfStep_restrict
    (d : ResidueFieldClosedStepData (B := B) i D.obj) :
    (residueFieldDiagramOfStep i D d).reindex
      (fun j : {j : K // j < i} ↦ ⟨j.val, j.property.le⟩)
      (fun _ _ h ↦ h) = D := by
  apply LocalAlgebraDiagram.ext
  · funext j
    exact algebraInitialSegmentObj_old i D.obj d.carrier j
  · apply Function.hfunext rfl
    intro j k hjk
    cases eq_of_heq hjk
    dsimp only [LocalAlgebraDiagram.reindex, residueFieldDiagramOfStep]
    with_unfolding_all
      change HEq ((inferInstance : CommRing (algebraSystemWithTopObj D.obj d.carrier
        ((initialSegmentWithTopEquiv i).symm ⟨j.val, j.property.le⟩)))) (D.ring j)
    rw [initialSegmentWithTopEquiv_symm_coe]
    with_unfolding_all rfl
  · apply Function.hfunext rfl
    intro j k hjk
    cases eq_of_heq hjk
    dsimp only [LocalAlgebraDiagram.reindex, residueFieldDiagramOfStep]
    with_unfolding_all
      change HEq ((inferInstance : Algebra B (algebraSystemWithTopObj D.obj d.carrier
        ((initialSegmentWithTopEquiv i).symm ⟨j.val, j.property.le⟩)))) (D.algebra j)
    rw [initialSegmentWithTopEquiv_symm_coe]
    with_unfolding_all rfl
  · apply Function.hfunext rfl
    intro j j' hj
    cases eq_of_heq hj
    apply Function.hfunext rfl
    intro k k' hk
    cases eq_of_heq hk
    apply Function.hfunext rfl
    intro h h' hh
    exact algebraInitialSegmentMap_old i D.obj d.carrier D.map d.incoming j k h
  · apply Function.hfunext rfl
    intro j k hjk
    cases eq_of_heq hjk
    exact algebraInitialSegmentTarget_old i D.obj d.carrier D.target d.target j

variable (hD : IsResidueFieldDiagram D (fun j ↦ residueGeneratorAfter (ResidueField B) K j.val))

/-- 実構成から選んだ延長を通常の図式へ移す。 -/
noncomputable def residueFieldExtendDiagram : LocalAlgebraDiagram B K {j : K // j ≤ i} := by
  let : DirectedSystem D.obj (D.map · · ·) := hD.1
  let : ∀ j, Module.Flat B (D.obj j) := hD.2.2.2.1
  exact residueFieldDiagramOfStep i D
    (residueFieldClosedStep i D.obj D.map D.target hD.2.2.2.2.2 hD.2.2.1 hD.2.1 hD.2.2.2.2.1)

include hD in
/-- 延長後も有向図式の法則・局所性・平坦性・極大イデアル・像が成立する。 -/
theorem residueFieldExtendDiagram_spec :
    IsResidueFieldDiagram (residueFieldExtendDiagram i D hD)
      (fun j ↦ residueGeneratorAfter (ResidueField B) K j.val) := by
  let : DirectedSystem D.obj (D.map · · ·) := hD.1
  let : ∀ j, Module.Flat B (D.obj j) := hD.2.2.2.1
  exact residueFieldDiagramOfStep_spec i D _
    (residueFieldClosedStep_spec i D.obj D.map D.target
      hD.2.2.2.2.2 hD.2.2.1 hD.2.1 hD.2.2.2.2.1)

include hD in
/-- 検証済み候補を選んだ後も、旧図式の構造と写像を保つ。 -/
theorem residueFieldExtendDiagram_restrict :
    (residueFieldExtendDiagram i D hD).reindex
      (fun j : {j : K // j < i} ↦ ⟨j.val, j.property.le⟩)
      (fun _ _ h ↦ h) = D := by
  let : DirectedSystem D.obj (D.map · · ·) := hD.1
  let : ∀ j, Module.Flat B (D.obj j) := hD.2.2.2.1
  exact residueFieldDiagramOfStep_restrict i D _

end DiagramExtension

section DiagramGlue

open IsLocalRing
variable {B K ι : Type u} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [LinearOrder ι]
variable (U : ι → Prop)
variable (p : ∀ j, U j → LocalAlgebraDiagram B K {k : ι // k ≤ j})
variable (hc : ∀ j k (hj : U j) (hk : U k) (hjk : j < k),
  localAlgebraHistoryRestrict j k hjk (p k hk) = p j hj)
variable (hU : ∀ {j l : ι}, j ≤ l → U l → U j)
variable (F : ι → IntermediateField (ResidueField B) K)
include hc hU

/-- 先行閉図式の法則を、実構成した開図式へ移す。 -/
theorem residueFieldDiagramLowerGlue_spec
    (hp : ∀ j h, IsResidueFieldDiagram (p j h)
      (fun k ↦ F k.val)) :
    IsResidueFieldDiagram (localAlgebraLowerGlue U p hc)
      (fun j ↦ F j.val) := by
  let D := localAlgebraLowerGlue U p hc
  have hE (l : ι) (hl : U l) :
      IsResidueFieldDiagram (D.reindex
        (fun j : {j : ι // j ≤ l} ↦ ⟨j.val, hU j.property hl⟩)
        (fun _ _ h ↦ h))
        (fun j ↦ F j.val) := by
    rw [localAlgebraLowerGlue_restrict U p hc hU l hl]
    exact hp l hl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro j x
      let E := D.reindex
        (fun k : {k : ι // k ≤ j.val} ↦ ⟨k.val, hU k.property j.property⟩)
        (fun _ _ h ↦ h)
      let : DirectedSystem E.obj (E.map · · ·) := (hE j.val j.property).1
      exact DirectedSystem.map_self' (F := E.obj) (f := E.map) (i := ⟨j.val, le_rfl⟩) x
    · intro k j a haj hjk x
      let E := D.reindex
        (fun q : {q : ι // q ≤ k.val} ↦ ⟨q.val, hU q.property k.property⟩)
        (fun _ _ h ↦ h)
      let : DirectedSystem E.obj (E.map · · ·) := (hE k.val k.property).1
      exact DirectedSystem.map_map' (F := E.obj) (f := E.map)
        (i := ⟨a.val, (show a.val ≤ j.val from haj).trans hjk⟩)
        (j := ⟨j.val, hjk⟩) (k := ⟨k.val, le_rfl⟩) haj hjk x
  · intro j k h
    exact (hE k.val k.property).2.1 ⟨j.val, h⟩ ⟨k.val, le_rfl⟩ h
  · intro j k h x
    exact (hE k.val k.property).2.2.1 ⟨j.val, h⟩ ⟨k.val, le_rfl⟩ h x
  · intro j
    exact (hp j.val j.property).2.2.2.1 ⟨j.val, le_rfl⟩
  · intro j
    exact (hp j.val j.property).2.2.2.2.1 ⟨j.val, le_rfl⟩
  · intro j
    exact (hp j.val j.property).2.2.2.2.2 ⟨j.val, le_rfl⟩

section Reindex
omit hc hU in
/-- 検証述語は単調な添字変更で保持される。 -/
theorem IsResidueFieldDiagram.reindex {J L : Type u} [Preorder J] [Preorder L]
    (D : LocalAlgebraDiagram B K J) (F : J → IntermediateField (ResidueField B) K)
    (hD : IsResidueFieldDiagram D F) (r : L → J) (hr : Monotone r) :
    IsResidueFieldDiagram (D.reindex r hr) (F ∘ r) := by
  let : DirectedSystem D.obj (D.map · · ·) := hD.1
  exact ⟨algebraSystemReindex_directedSystem D.obj D.map r hr,
    algebraSystemReindex_isLocalHom D.obj D.map r hr hD.2.1,
    algebraSystemReindexTarget_compatible D.obj D.map r hr D.target hD.2.2.1,
    (fun j ↦ hD.2.2.2.1 (r j)), (fun j ↦ hD.2.2.2.2.1 (r j)),
    (fun j ↦ hD.2.2.2.2.2 (r j))⟩
end Reindex

section All
variable (q : ∀ j : ι, LocalAlgebraDiagram B K {k : ι // k ≤ j})
variable (hq : ∀ j k (hjk : j < k), localAlgebraHistoryRestrict j k hjk (q k) = q j)
omit hc hU in
/-- 全体図式の法則も、同じ貼り合わせの保存定理から得る。 -/
theorem residueFieldDiagramGlueAll_spec
    (hp : ∀ j, IsResidueFieldDiagram (q j) (fun k ↦ F k.val)) :
    IsResidueFieldDiagram (localAlgebraGlueAll q hq) F := by
  exact IsResidueFieldDiagram.reindex _ _
    (residueFieldDiagramLowerGlue_spec (fun _ : ι ↦ True) (fun j _ ↦ q j)
    (fun j k _ _ hjk ↦ hq j k hjk) (fun _ _ ↦ trivial) F
    (fun j _ ↦ hp j))
    (fun j ↦ ⟨j, trivial⟩) (fun _ _ h ↦ h)
end All

end DiagramGlue

section History

open IsLocalRing
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

end History

section HistoryGlue

open IsLocalRing
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

end HistoryGlue

end SerrePositivity
