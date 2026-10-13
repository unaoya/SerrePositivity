module

public import Mathlib.Logic.Function.Basic
public import SerrePositivity.CommutativeAlgebra.LocalAlgebraDiagram
public import SerrePositivity.CommutativeAlgebra.ResidueFieldClosedStep

/-! # 剰余体拡大の図式としての一段延長

図式のデータと、その法則・平坦性・極大イデアル・指定中間体への像を分ける。
検証済みの開初期部分から、通常の閉初期部分の図式を構成する。
-/

@[expose] public section
namespace SerrePositivity
open IsLocalRing
universe u
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

end SerrePositivity
