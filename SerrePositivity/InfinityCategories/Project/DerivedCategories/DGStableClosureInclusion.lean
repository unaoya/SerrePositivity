module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableSubcategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedStability
/-!
概要：指定対象の実安定閉包の包含と、完全関手による零化の同値。
方針：実安定閉包の帰納法と包含の実頂点の式を使う。
規約：全頂点について零化する。使われ方：指定対象の零化から Verdier 列への移行。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 元の実安定閉包の包含。 -/
def dgStableClosureInclusion (P : Set D) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve A D P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty A D P))
/-- 指定対象の実安定閉包からなる nerve は安定。 -/
lemma dgStableClosureNerve_isStable (P : Set D) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve A D P) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated A D
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableSubcategory_isStable A D _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty_isStable A D P)
/-- 安定閉包の包含は完全。 -/
lemma dgStableClosureInclusion_isExactFunctor (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgStableClosureInclusion A D P) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated A D
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableSubcategoryInclusion_isExactFunctor A D _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty_isStable A D P)
omit [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 安定閉包の包含は全写像空間で充満忠実。 -/
lemma dgStableClosureInclusion_isFullyFaithful (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgStableClosureInclusion A D P) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful A D _
/-- 完全関手が指定対象を零化すれば、安定閉包の包含との合成の全頂点を零化する。 -/
lemma dgStableClosureInclusion_kills {Y : SSet.{max u v}} [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (P : Set D) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]
    (h : ∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
    (z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve A D P) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((dgStableClosureInclusion A D P ≫ F).app (Opposite.op ⦋0⦌) z) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated A D
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map _).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kills_stableVertexClosure F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P)
    (by rintro _ ⟨a, ha, rfl⟩; exact h a ha) x.property
/-- 安定閉包全体の零化と、元の指定対象の零化は同値。 -/
lemma dgStableClosureInclusion_kills_iff {Y : SSet.{max u v}} [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (P : Set D) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] :
    (∀ z, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((dgStableClosureInclusion A D P ≫ F).app (Opposite.op ⦋0⦌) z)) ↔
      ∀ x ∈ P, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) := by
  constructor
  · intro h x hx
    let a : DGFullSubcategory D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty A D P) :=
      ⟨x, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem ⟨x, hx, rfl⟩⟩
    have hz := h (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex a)
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map _).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex a))) at hz
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at hz
    exact hz
  · intro h
    exact dgStableClosureInclusion_kills A D P F h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
