module
public import SerrePositivity.InfinityCategories.Derived.DGKappaSphereClosurePerfectCovers
public import SerrePositivity.InfinityCategories.Derived.DGKappaClosedProjectiveProperty
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UnconditionalConeInput

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
include hκ hreg

lemma dgKappaSphereClosureObjects_subset (M : ModuleCategory R D)
    (hM : dgKappaSphereClosureObjects R D κ M) : dgKappaClosedProjectiveObjects R D κ M := by
  obtain ⟨⟨a, i⟩, rfl⟩ := hM
  apply dgProjectiveClosureStage_property R D (dgKappaClosedProjectiveObjects R D κ)
    (dgKappaClosedProjectiveObjects_zero R D hκ)
    (fun M h s => dgKappaClosedProjectiveObjects_shift R D hκ hreg M h s)
    (dgKappaClosedProjectiveObjects_binaryClosed R D hκ hreg)
    (dgKappaClosedProjectiveObjects_cone R D hκ hreg)
    (dgKappaClosedProjectiveObjects_countableClosed R D hκ hreg)
    (dgKappaSphereClosureBaseFamily R D κ) _ a i
  intro j
  exact dgKappaClosedProjectiveObjects_sphereFree R D hκ j

lemma dgKappaSphereClosureObjects_oldHomotopyCovers (M : ModuleCategory R D)
    (hM : dgKappaClosedProjectiveObjects R D κ M) :
    dgModuleHomotopyRange R D (dgKappaSphereClosureObjects R D κ) M := by
  apply dgKappaClosedProjectiveObjects_property R D
    (dgModuleHomotopyRange R D (dgKappaSphereClosureObjects R D κ))
    (dgModuleHomotopyRange_of_mem R D _ (dgKappaSphereClosureObjects_zero R D hκ))
    (fun M h s => dgModuleHomotopyRange_shift R D _
      (fun N hn s => dgKappaSphereClosureObjects_shift R D hκ hreg N hn s) h s)
    (fun M N hm hn => dgModuleHomotopyRange_binary R D _
      (dgKappaSphereClosureObjects_binaryClosed R D hκ hreg) hm hn)
    (fun M N hm hn f => dgModuleHomotopyRange_cone R D _
      (dgKappaSphereClosureObjects_cone R D hκ hreg) hm hn f)
    (fun M hm => dgModuleHomotopyRange_coproduct R D _
      (dgKappaSphereClosureObjects_countableClosed R D hκ hreg) M hm)
    (fun i => dgModuleHomotopyRange_of_mem R D _
      (dgKappaSphereClosureObjects_sphereFree R D hκ i)) ?_ M hM
  intro i
  exact dgKappaSphereClosureObjects_perfectHomotopyCovers R D hκ hreg _
    (dgKappaPerfectRepresentative_projective R D i)
    (perfectDGModuleRepresentative R D Set.univ i).property.2

lemma dgKappaSphereClosureObjects_derivedFullyFaithful :
    IsFullyFaithful
      (dgNerve.map (dgFullSubcategoryInclusion R (ModuleCategory R D)
        (dgKappaSphereClosureObjects R D κ)) ≫ dgConeModuleDerived R D) :=
  dgProjectiveSubcategoryConeDerived_isFullyFaithful R D _
    (dgKappaSphereClosureObjects_projective R D κ)

variable [Fact κ.IsRegular]

lemma dgKappaSphereClosureObjects_isKappaCompact (M : ModuleCategory R D)
    (hM : dgKappaSphereClosureObjects R D κ M) : dgModuleKappaCompact R D κ M :=
  dgBarCompactClosedProjective_isKappaCompact R D κ hκ M
    (dgKappaSphereClosureObjects_subset R D hκ hreg M hM)

lemma dgKappaSphereClosure_covers_unconditional
    (y : (dgModuleDerivedInfinityCategory R D) _⦋0⦌)
    (hy : F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ y) :
    ∃ N : ModuleCategory R D, dgKappaSphereClosureObjects R D κ N ∧
      Nonempty (VertexIso (dgConeModuleDerivedVertex R D N) y) := by
  obtain ⟨M, hM, ⟨eM⟩⟩ := dgKappaCone_covers_unconditional R D κ hκ y hy
  obtain ⟨N, hN, ⟨e⟩⟩ := dgKappaSphereClosureObjects_oldHomotopyCovers R D hκ hreg M hM
  let eD := ((moduleToHomotopyDerivedIso R D).app N).symm ≪≫
    (moduleHomotopyToDerivedClosed R D).mapIso e ≪≫ (moduleToHomotopyDerivedIso R D).app M
  exact ⟨N, hN, ⟨dgConeModuleDerivedVertexIsoOfDerivedIso R D eD ≪≫ eM⟩⟩

end SerrePositivity.InfinityCategories
