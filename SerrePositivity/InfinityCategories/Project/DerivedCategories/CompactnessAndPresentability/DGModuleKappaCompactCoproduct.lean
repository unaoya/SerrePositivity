module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGProjectiveCoproductCocone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGModuleKappaCompactProjectiveComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaDiscretePosetShape
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGModuleKappaCompactCone
/-!
概要：同じ実導来加群頂点の κ-compact 性は κ 未満の直和で閉じる。
方針：射影的直和の実 coherent 余錐へ P-9 を適用し、実分解と準同型比較で戻す。
規約：正則非可算 κ と元の全 Hom の compact 性を使い、交換の追加入力を残さない。
使われ方：D-8 c5 の可算直和と c2 の球面自由基底への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet

open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
variable {κ : Cardinal.{u}} [hreg : Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
include hreg hκ

lemma dgProjectiveCoproduct_isKappaCompact {J : Type u} (hJ : HasCardinalLT J κ)
    (M : J → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
    (hM : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (ForgetEnrichment.of (Complex R) (M j).val)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (∐ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveCoproductUnderlying R D M) := by
  let c := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveCoproductCofan R D M)
  let e := (SSet.uliftFunctor.{max (u+1) v, u}).mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaDiscretePosetNerveIso J)
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveCoproductCofan_isColimitCone R D M
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallPosetColimit_universe.{u, max (u+1) v}
    hκ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaDiscretePoset J) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaDiscretePoset_hasCardinalLT J hJ)
    (c.restrict e.hom) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso c e.hom).mp hc) (fun k => ?_)
  · have hv : (c.restrict e.hom).vertex = c.vertex := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq]
      change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap e.hom (𝟙 _) ≫ c.val)) = _
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
    rw [hv] at hp
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u+1) v} κ c.vertex at hp
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_vertex] at hp
    have hv' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (ForgetEnrichment.of (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveCoproductObject R D M)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveCoproductObject R D M) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object (C := ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveCoproductObject R D M))
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u+1) v} κ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (ForgetEnrichment.of (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveCoproductObject R D M))) at hp
    rw [hv'] at hp
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_iff_projectiveCoherentVertex R D
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveCoproductObject R D M)).mpr hp
  · rcases k with ⟨k⟩
    have hk : k = ComposableArrows.mk₀ (k.obj 0) := ComposableArrows.ext₀ rfl
    rw [hk]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u+1) v} κ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (Discrete.functor (fun j =>
        ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (M j)))).app _
          (ULift.up (ComposableArrows.mk₀ ⟨(k.obj 0).val⟩)))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex]
    have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (ForgetEnrichment.of (Complex R) (M (k.obj 0).val)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) (M (k.obj 0).val) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object (C := ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) (M (k.obj 0).val))
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u+1) v} κ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (ForgetEnrichment.of (Complex R) (M (k.obj 0).val)))
    rw [hv]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_iff_projectiveCoherentVertex R D _).mp (hM _)

lemma dgModuleKappaCompact_coproduct {J : Type u} (hJ : HasCardinalLT J κ)
    (M : J → ModuleCategory R D) (hM : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (M j)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (∐ M) := by
  let P := fun j => _root_.SerrePositivity.DifferentialGraded.moduleCanonicalProjectiveResolution R D (M j)
  let Q : J → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D := fun j =>
    ⟨ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (P j).obj, (P j).projective⟩
  have hQ := dgProjectiveCoproduct_isKappaCompact R D hκ hJ Q (fun j =>
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_iff_of_quasiIso R D (P j).π (P j).quasiIso).mpr (hM j))
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_iff_of_quasiIso R D (Limits.Sigma.map (fun j => (P j).π))
    (_root_.SerrePositivity.DifferentialGraded.module_coproductMap_quasiIso R D _ (fun j => (P j).quasiIso))).mp hQ

lemma dgModuleKappaCompact_countableCoproduct (M : ℕ → _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)
    (hM : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (M n)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (∐ M) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_iff_of_iso R D (Sigma.reindex Equiv.ulift M)).mp
  apply dgModuleKappaCompact_coproduct R D hκ
    (J := ULift.{u} ℕ) (M := fun n => M n.down)
  · simpa [HasCardinalLT] using hκ
  · intro n
    exact hM n.down

end SerrePositivity.InfinityCategories.Project.DerivedCategories
