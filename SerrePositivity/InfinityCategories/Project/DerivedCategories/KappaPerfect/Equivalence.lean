module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.Closure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectYonedaIdempotentCompletion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful

/-!
概要：同じ cone 内の perfect 安定閉包から元の実 Perf への全 Hom 比較同値。
方針：同じ加群と全 Hom を保つ dg 関手を作り、perfectCovers を頂点同型へ戻す。
規約：通常の導来同型は本質的全射性にのみ使う。使われ方：D-8 e の逆関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 安定閉包の同じ実加群を、元の射影的 perfect dg 模型へ送る。 -/
def dgKappaPerfectToPerf : _root_.SerrePositivity.DifferentialGraded.DGFunctor R
    (_root_.SerrePositivity.DifferentialGraded.DGFullSubcategory (DGKappaCone R D I)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)))
    (_root_.SerrePositivity.DifferentialGraded.PerfectDGModule R D) where
  obj M := ⟨ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M.val.val,
    I.projective M.val.val M.val.property,
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfect_stableClosure_iff R D I M.val).mp M.property⟩
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp _ _ _ := by
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
    rfl

/-- 同じ全 dg Hom の恒等写像による逆向き比較。 -/
def dgKappaPerfectReverse := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaPerfectToPerf R D I)

lemma dgKappaPerfectReverse_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgKappaPerfectReverse R D I) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_homIso
  intro M N
  change IsIso (𝟙 _)
  infer_instance

/-- perfectCovers の主導来同型を、元の実 Perf 内の頂点同型へ戻す。 -/
lemma dgKappaPerfectReverse_isEssentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (dgKappaPerfectReverse R D I) := by
  intro z
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
  let M₀ := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M.val
  obtain ⟨N, hN, ⟨e⟩⟩ := I.perfectCovers M₀ M.property.2
  have hp : _root_.SerrePositivity.DifferentialGraded.modulePerfect R D ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj N) :=
    (_root_.SerrePositivity.DifferentialGraded.modulePerfect R D).prop_of_iso e.symm M.property.2
  let x : _root_.SerrePositivity.DifferentialGraded.DGFullSubcategory (DGKappaCone R D I)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)) :=
    ⟨⟨N, hN⟩, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem ⟨⟨N, hN⟩, hp, rfl⟩⟩
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x, ⟨?_⟩⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaPerfectToPerf R D I)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectDerivedHoComparison R D).preimageIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectVertex_classicalIso R D ((dgKappaPerfectToPerf R D I).obj x) ≪≫ e ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectVertex_classicalIso R D M).symm)

/-- 全写像空間の同値と実頂点の被覆による QCat 同値。 -/
theorem dgKappaPerfectReverse_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgKappaPerfectReverse R D I) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (dgKappaPerfectReverse_isFullyFaithful R D I)
    (dgKappaPerfectReverse_isEssentiallySurjective R D I)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect
