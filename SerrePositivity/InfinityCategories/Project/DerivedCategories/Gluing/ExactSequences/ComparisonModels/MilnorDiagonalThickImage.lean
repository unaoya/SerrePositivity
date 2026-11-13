module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.MilnorDiagonalStableImage
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGThickKernelNativeRetract
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectIdempotentCompleteGeneral
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompleteImageRetracts
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
lemma dgGluingMilnorDiagonalSource_isIdempotentComplete :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source))) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleNerve_isIdempotentComplete R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source)).of_equivalence
    (dgSmallPerfectEnvelopeNerveEquivalence R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source) Empty
      (dgSmallPerfectBaseFamily R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source))).symm
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d)]
  [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal)]
lemma dgGluingMilnorDiagonal_thickClosure_iff_image
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) (hgen : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSmallPerfectGeneration R d)
    (x : DGOdotGluing R d) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty R (DGOdotGluing R d)
      (dgQuotientImage R (dgOdotQuotientInput R d).diagonal) x ↔
    ∃ a : DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) ((dgOdotQuotientInput R d).diagonal.obj a))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) x)) := by
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R (DGOdotGluing R d)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty_iff_nativeStableRetract]
  constructor
  · rintro ⟨y, hy, ⟨r⟩⟩
    obtain ⟨a, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonal_stableClosure_image R d h hgen y hy
    have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSmallPerfectDiagonal_isFullyFaithful R d h hgen
    let r' := r.trans (Retract.ofIso e.symm)
    obtain ⟨a', ⟨e'⟩⟩ :=
      (dgGluingMilnorDiagonalSource_isIdempotentComplete R d).retract_iso_in_image
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal) hf
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) x) (by
          rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
          exact r')
    obtain ⟨a', rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective a'
    erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at e'
    exact ⟨a', ⟨e'.symm⟩⟩
  · rintro ⟨a, ⟨e⟩⟩
    exact ⟨_, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem ⟨_, ⟨a, rfl⟩, rfl⟩,
      ⟨Retract.ofIso e.symm⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
