module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.InfinityCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuasiEquivalenceNerve
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UnconditionalConeInput
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.SemifreeNativeColimit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFamilyGeneratorTransport
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableEquivalence

/-!
概要：可換環上の半自由複体の dg nerve は presentable である。
方針：一対象 dg 加群模型の κ-compact な小さい代表系を使い、半自由解像度を
κ-filtered な部分分解の余極限として表示する。比較を元の半自由複体へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Presentable
open CategoryTheory Limits SSet DifferentialGraded
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

private instance smallFixedSimplex {D : Type (u + 1)} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
    (v : Fin (n + 1) → D) : Small.{u} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n // s.obj = v} := by
  let code (s : {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n // s.obj = v}) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily A D v := s.property ▸ s.val.hom
  apply small_of_injective (f := code)
  rintro ⟨⟨⟨w, f⟩, hf⟩, rfl⟩ ⟨⟨⟨w', g⟩, hg⟩, he⟩ h
  cases he
  change f = g at h
  cases h
  rfl

private lemma smallFixedMaps (D : Type (u + 1)) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) := by
  intro K hK v
  let := hK
  let obj (n : SimplexCategoryᵒᵖ) (s : K.obj n) (i : Fin (n.unop.len + 1)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A D (v (K.map (SimplexCategory.const ⦋0⦌ n.unop i).op s))
  let code (f : {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D // ∀ a, f.app _ a = v a}) :
      ∀ (n : SimplexCategoryᵒᵖ) (s : K.obj n),
        {z : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n.unop.len // z.obj = obj n s} := fun n s =>
    ⟨f.val.app n s, funext fun i => by
      let j := (SimplexCategory.const ⦋0⦌ n.unop i).op
      have h := ConcreteCategory.congr_hom (f.val.naturality j) s
      exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A D) (h.symm.trans (f.property _))⟩
  apply small_of_injective (f := code)
  intro f g h
  apply Subtype.ext
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact congrArg Subtype.val (congrFun (congrFun h n) s)

private abbrev B := PUnit.{1}
private abbrev ModNerve := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory A B
private abbrev κ : Cardinal.{u} := Cardinal.aleph 1
private instance : Fact κ.{u}.IsRegular := ⟨Cardinal.isRegular_aleph_one⟩
private lemma hκ : Cardinal.aleph0 < κ.{u} := Cardinal.aleph0_lt_aleph_one

private abbrev Reps := {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A B // _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects A B κ M}
private instance : Small.{u} (Reps A) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_small A B κ
private def generator (t : Shrink.{u} (Reps A)) : (ModNerve A) _⦋0⦌ :=
  dgConeModuleDerivedVertex A B ((equivShrink (Reps A)).symm t).val

private lemma generator_compact (t : Shrink.{u} (Reps A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (generator A t) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactClosedProjective_isKappaCompact A B κ hκ _ ((equivShrink (Reps A)).symm t).property

private lemma module_presentable : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (ModNerve A) := by
  have hc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (ModNerve A) := fun _ G => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgSemifreeCoherent_hasColimit A B G
  let hsmall := smallFixedMaps A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules A B)
  refine ⟨⟨κ, Cardinal.isRegular_aleph_one, hc.hasSmallKappaFilteredColimits κ,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModel hsmall (generator A), inferInstance,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion hsmall (generator A), ?_⟩, hc⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion_isKappaCompactGenerating hsmall (generator A) (generator_compact A)
  intro x
  obtain ⟨P, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  let M := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) P.val
  let p := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionStrictRepresentativePresentation A B M κ hκ
  let := p.order
  let := p.filtered
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered (κ := κ) p.Index
  obtain ⟨c, hc, ⟨ec⟩⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgKappaStrictFilteredColimitComparison_unconditional A B κ
    p.Index p.diagram p.cocone p.isColimit
  refine ⟨nerve p.Index, inferInstance, inferInstance, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaStrictModuleDiagram A B p.diagram,
    ?_, ?_⟩
  · intro i
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaStrictModuleDiagram_vertex]
    obtain ⟨N, hN, ⟨e⟩⟩ := p.stageCovers (i.obj 0)
    refine ⟨equivShrink (Reps A) ⟨N, hN⟩, ?_⟩
    simp only [generator, Equiv.symm_apply_apply]
    exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertexIsoOfDerivedIso A B e.symm⟩
  · let eM := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertexIsoOfDerivedIso A B
      ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived A B).mapIso p.iso ≪≫ _root_.SerrePositivity.DifferentialGraded.moduleDerivedIso A B (_root_.SerrePositivity.DifferentialGraded.moduleResolutionCandidateπ A B M)
        (_root_.SerrePositivity.DifferentialGraded.moduleResolutionCandidateπ_quasiIso A B M))
    let H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedHoComparison A B
    have hi : H.obj (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P)) ≅
        (_root_.SerrePositivity.DifferentialGraded.moduleToDerived A B).obj M := (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso A B).app M
    let eP : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgConeModuleDerivedVertex A B M) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P) :=
      H.preimageIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertex_classicalIso A B M ≪≫ hi.symm)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_colimitCone_vertex_of_iso c hc (ec ≪≫ eM ≪≫ eP)

private def ringInclusion : _root_.SerrePositivity.DifferentialGraded.DGFunctor A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules A B) where
  obj P := ⟨(_root_.SerrePositivity.DifferentialGraded.ringConstantDG A).obj P.val, P.property⟩
  map P Q := (_root_.SerrePositivity.DifferentialGraded.ringConstantDG A).map P.val Q.val
  map_id P := (_root_.SerrePositivity.DifferentialGraded.ringConstantDG A).map_id P.val
  map_comp P Q T := (_root_.SerrePositivity.DifferentialGraded.ringConstantDG A).map_comp P.val Q.val T.val

private lemma ringInclusion_equivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (ringInclusion A)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.qCatEquivalenceOfFullyFaithfulEssentiallySurjective _ _ _).isQCatEquivalence
  · apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_quasiIso
    intro P Q
    exact (_root_.SerrePositivity.DifferentialGraded.ringConstantDG_quasiEquivalence A).1 P.val Q.val
  · intro y
    obtain ⟨P, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
    let N := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) P.val
    let Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A :=
      ⟨P.val.obj (.op PUnit.unit), (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree_evaluation A N).mpr P.property⟩
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q, ?_⟩
    have he : (ringInclusion A).obj Q = P := Subtype.ext (_root_.SerrePositivity.DifferentialGraded.ringModule_recover A P.val)
    exact ⟨eqToIso (congrArg SSet.HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex _ Q).trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := A)) he)))⟩

/-- 小さい A 加群の非有界導来 ∞ 圏は同じ宇宙で presentable。 -/
lemma derivedInfinityCategory_isPresentable :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) :=
  (module_presentable A).of_equivalence (ringInclusion_equivalence A).choose.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Presentable
