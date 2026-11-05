module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorDiagonalStableImage
public import SerrePositivity.InfinityCategories.Derived.DGThickKernelNativeRetract
public import SerrePositivity.InfinityCategories.Derived.DGPerfectIdempotentCompleteGeneral
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompleteImageRetracts
/-!
概要：元小 Perf 対角像の実 thick 閉包は、その同じ対角の本質像と一致する。
方針：安定閉包の対象を元対角の像へ戻し、始域の冪等完備性で retract を回収する。
規約：D-17 の生成入力と、D-18 から接続する前三角性・完全性を分離する。
使われ方：同じ cell 平坦商の核を元の Milnor 対角に接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
lemma dgGluingMilnorDiagonalSource_isIdempotentComplete :
    F2.Idempotent.IsIdempotentComplete
      (dgNerve R (DGSmallPerfectBase R (dgAlgebraCategory R d.source))) := by
  exact (dgPerfectModuleNerve_isIdempotentComplete R (dgAlgebraCategory R d.source)).of_equivalence
    (dgSmallPerfectEnvelopeNerveEquivalence R (dgAlgebraCategory R d.source) Empty
      (dgSmallPerfectBaseFamily R (dgAlgebraCategory R d.source))).symm
variable [IsDGPretriangulated R (DGOdotGluing R d)]
  [IsExactFunctor (dgNerve.map (dgOdotQuotientInput R d).diagonal)]
lemma dgGluingMilnorDiagonal_thickClosure_iff_image
    (h : DGGluingMilnorSquare R d) (hgen : DGGluingMilnorSmallPerfectGeneration R d)
    (x : DGOdotGluing R d) :
    dgThickClosureProperty R (DGOdotGluing R d)
      (dgQuotientImage R (dgOdotQuotientInput R d).diagonal) x ↔
    ∃ a : DGSmallPerfectBase R (dgAlgebraCategory R d.source),
      Nonempty (VertexIso (X := dgNerve R (DGOdotGluing R d))
        (Simplex.vertex (A := R) ((dgOdotQuotientInput R d).diagonal.obj a))
        (Simplex.vertex (A := R) x)) := by
  let := dgNerve_isStable_of_pretriangulated R (DGOdotGluing R d)
  rw [dgThickClosureProperty_iff_nativeStableRetract]
  constructor
  · rintro ⟨y, hy, ⟨r⟩⟩
    obtain ⟨a, ⟨e⟩⟩ := dgGluingMilnorDiagonal_stableClosure_image R d h hgen y hy
    have hf := dgGluingMilnorSmallPerfectDiagonal_isFullyFaithful R d h hgen
    let r' := r.trans (Retract.ofIso e.symm)
    obtain ⟨a', ⟨e'⟩⟩ :=
      (dgGluingMilnorDiagonalSource_isIdempotentComplete R d).retract_iso_in_image
        (dgNerve.map (dgOdotQuotientInput R d).diagonal) hf
        (Simplex.vertex (A := R) a) (Simplex.vertex (A := R) x) (by
          rw [dgFunctorNerve_vertex]
          exact r')
    obtain ⟨a', rfl⟩ := Simplex.vertexEquiv.symm.surjective a'
    erw [dgFunctorNerve_vertex] at e'
    exact ⟨a', ⟨e'.symm⟩⟩
  · rintro ⟨a, ⟨e⟩⟩
    exact ⟨_, StableVertexClosure.of_mem ⟨_, ⟨a, rfl⟩, rfl⟩,
      ⟨Retract.ofIso e.symm⟩⟩
end SerrePositivity.InfinityCategories
