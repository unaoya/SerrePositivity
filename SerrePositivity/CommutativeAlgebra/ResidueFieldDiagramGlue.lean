module

public import SerrePositivity.CommutativeAlgebra.LocalAlgebraDiagramLowerGlue
public import SerrePositivity.CommutativeAlgebra.ResidueFieldDiagramExtension

/-! # 下方に閉じた添字集合での剰余体図式の法則の保存

通常の局所代数図式の貼り合わせへ、平坦性・極大イデアル・指定中間体の像を接続する。
開初期部分と全添字集合で同じ保存定理を適用する。
-/

@[expose] public section
namespace SerrePositivity
open IsLocalRing
universe u
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

end SerrePositivity
