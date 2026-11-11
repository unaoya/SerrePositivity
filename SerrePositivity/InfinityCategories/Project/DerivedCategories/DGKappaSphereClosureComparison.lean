module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereClosurePerfectCovers
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedProjectiveProperty
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.UnconditionalConeInput

/-!
概要：旧族の被覆を、新しい sphere-only 閉包族へ同じ実導来圏内で移す。
方針：新族の旧族への所属と、旧族の新族によるホモトピー被覆を別々に証明する。
規約：新族の基底に perfect 小模型を戻さない。旧族の定義・証明は編集しない。
使われ方：D-2 の covers・κ-compact 性・全写像空間比較の無条件供給。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
include hκ hreg

lemma dgKappaSphereClosureObjects_subset (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)
    (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ M) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M := by
  obtain ⟨⟨a, i⟩, rfl⟩ := hM
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage_property R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_zero R D hκ)
    (fun M h s => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_shift R D hκ hreg M h s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_binaryClosed R D hκ hreg)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_cone R D hκ hreg)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_countableClosed R D hκ hreg)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureBaseFamily R D κ) _ a i
  intro j
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_sphereFree R D hκ j

lemma dgKappaSphereClosureObjects_oldHomotopyCovers (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)
    (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ) M := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_property R D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange_of_mem R D _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_zero R D hκ))
    (fun M h s => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange_shift R D _
      (fun N hn s => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_shift R D hκ hreg N hn s) h s)
    (fun M N hm hn => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange_binary R D _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_binaryClosed R D hκ hreg) hm hn)
    (fun M N hm hn f => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange_cone R D _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_cone R D hκ hreg) hm hn f)
    (fun M hm => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange_coproduct R D _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_countableClosed R D hκ hreg) M hm)
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange_of_mem R D _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_sphereFree R D hκ i)) ?_ M hM
  intro i
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_perfectHomotopyCovers R D hκ hreg _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPerfectRepresentative_projective R D i)
    (_root_.SerrePositivity.DifferentialGraded.perfectDGModuleRepresentative R D Set.univ i).property.2

lemma dgKappaSphereClosureObjects_derivedFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (ModuleCategory R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ)) ≫ dgConeModuleDerived R D) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveSubcategoryConeDerived_isFullyFaithful R D _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_projective R D κ)

variable [Fact κ.IsRegular]

lemma dgKappaSphereClosureObjects_isKappaCompact (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)
    (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ M) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactClosedProjective_isKappaCompact R D κ hκ M
    (dgKappaSphereClosureObjects_subset R D hκ hreg M hM)

lemma dgKappaSphereClosure_covers_unconditional
    (y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u + 1) v} κ y) :
    ∃ N : ModuleCategory R D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ N ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgConeModuleDerivedVertex R D N) y) := by
  obtain ⟨M, hM, ⟨eM⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCone_covers_unconditional R D κ hκ y hy
  obtain ⟨N, hN, ⟨e⟩⟩ := dgKappaSphereClosureObjects_oldHomotopyCovers R D hκ hreg M hM
  let eD := ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app N).symm ≪≫
    (_root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R D).mapIso e ≪≫ (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app M
  exact ⟨N, hN, ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertexIsoOfDerivedIso R D eD ≪≫ eM⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
