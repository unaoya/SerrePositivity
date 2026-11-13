module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRepleteYoneda
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGVertexIsoOfH0
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-! # ホモトピー表現可能部分との明示的 ∞ 圏同値

概要：対象宇宙を上げた任意の dg 圏の nerve はホモトピー表現可能部分と同値。
方針：H⁰ 包含の完全忠実性で代表加群との同型を反映し、Core の実頂点同型へ送る。
規約：前三角性は不要。使われ方：前三角 dg 圏の安定性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- ホモトピー表現可能な対象は、内部でも代表加群の頂点と実同型になる。 -/
lemma dgRepleteRepresentable_vertex_iso (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepleteRepresentables A D) :
    ∃ x : D, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepleteRepresentables A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYoneda A D).obj ⟨ULift.up x⟩)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)) := by
  obtain ⟨x, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff A D _).1 M.property
  let R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepleteRepresentables A D :=
    ⟨representable A x, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable_representable A D x⟩
  let F := dgFullSubcategoryInclusion A (RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable A D)
  let e' : (toHomotopy A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepleteRepresentables A D)).obj
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) M) ≅
      (toHomotopy A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepleteRepresentables A D)).obj
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) R) := F.onHomotopy.preimageIso e
  exact ⟨x, ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexIsoOfH0 A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepleteRepresentables A D) e'.symm⟩⟩

/-- 実 dg Yoneda の nerve はホモトピー表現可能部分の全対象を同値まで覆う。 -/
lemma dgRepleteYonedaNerve_isEssentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYoneda A D)) := by
  intro y
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  obtain ⟨x, e⟩ := dgRepleteRepresentable_vertex_iso A D M
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨ULift.up x⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u + 1) v} D), ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
  exact e

/-- 共通宇宙の元の dg nerve とホモトピー表現可能部分の明示的 ∞ 圏同値。 -/
def dgRepleteYonedaNerveEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u + 1) v} D))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentableNerve A D) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.qCatEquivalenceOfFullyFaithfulEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYoneda A D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYonedaNerve_isFullyFaithful A D) (dgRepleteYonedaNerve_isEssentiallySurjective A D)

/-- 明示的同値の順方向は実 dg Yoneda の nerve そのもの。 -/
lemma dgRepleteYonedaNerveEquivalence_hom :
    (dgRepleteYonedaNerveEquivalence A D).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYoneda A D) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
