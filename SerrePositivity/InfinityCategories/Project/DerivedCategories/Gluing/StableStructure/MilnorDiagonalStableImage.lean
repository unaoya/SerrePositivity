module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.MilnorSmallPerfectFaithfulness
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableClosureFullyFaithful
/-!
概要：元小 Perf 対角の安定閉包は、同じ対角の実本質像に含まれる。
方針：完全充満忠実な h 圏関手の像に安定生成性を適用する。
規約：安定性と完全性は補助段階の入力。対角・対象ラベルは選び直さない。
使われ方：D-16 の retract 判定から元対角の thick 核を回収する前段。
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
  [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d))]
  [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal)]
lemma dgGluingMilnorDiagonal_stableClosure_image
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) (hgen : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSmallPerfectGeneration R d)
    (y : DGOdotGluing R d)
    (hy : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) '' dgQuotientImage R (dgOdotQuotientInput R d).diagonal)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) y)) :
    ∃ a : DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) ((dgOdotQuotientInput R d).diagonal.obj a))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) y)) := by
  let := dgSmallPerfectBaseNerve_isStable R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source)
  let H := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal)).toFunctor
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSmallPerfectDiagonal_isFullyFaithful R d h hgen
  let : H.Full := hf.toHoFullyFaithful.full
  let : H.Faithful := hf.toHoFullyFaithful.faithful
  let T := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure
    (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source))) Set.univ
  have hle : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) ''
        dgQuotientImage R (dgOdotQuotientInput R d).diagonal) ≤ T.map H := by
    refine (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure_le_iff (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) '' dgQuotientImage R (dgOdotQuotientInput R d).diagonal)
      (T.map H)).mpr ?_
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    have ha := T.prop_map_obj H (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) a))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem (Set.mem_univ _))
    change (T.map H) ((SSet.mapHomotopyCategory
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal)).obj _) at ha
    rw [SSet.mapHomotopyCategory_obj_mk, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at ha
    exact ha
  obtain ⟨a, _, ⟨e⟩⟩ := hle (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) y)) hy
  obtain ⟨v, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨a, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective v
  refine ⟨a, ⟨?_⟩⟩
  change (SSet.mapHomotopyCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal)).obj
    (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) a)) ≅
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) y) at e
  rw [SSet.mapHomotopyCategory_obj_mk, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at e
  exact e
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
