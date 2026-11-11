module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleKappaCompactCoproduct
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleKappaCompactPerfectCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedProjectiveProperty
public import SerrePositivity.DifferentialGraded.Module.TensorFree
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
/-!
概要：代表加群の native κ-compact 性を、現 κ-small 代表模型の七入力へ伝える。
方針：球面自由項を代表加群の shift と比較し、κ 未満直和・perfect retract・演算木を適用する。
規約：代表加群の全 Hom に関する compact 性は明示入力であり、ordinary compact 性で代用しない。
使われ方：D-8 c2 の残る生成元証明を c6・c7 へ接続する帰着。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
variable {κ : Cardinal.{u}} [hreg : Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
include hreg hκ

lemma dgModuleKappaCompact_smallCoproduct {J : Type w} [Small.{u} J]
    (hJ : HasCardinalLT J κ) (M : J → ModuleCategory R D)
    (hM : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (M j)) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (∐ M) := by
  let e : Shrink.{u} J ≃ J := (equivShrink.{u} J).symm
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_iff_of_iso R D (Sigma.reindex e M)).mp
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_coproduct R D hκ
    ((hasCardinalLT_iff_of_equiv e κ).mpr hJ) (M ∘ e) (fun j => hM (e j))

omit hreg hκ in
lemma dgModuleKappaCompact_freeSphere
    (hgen : ∀ x : D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ
      (ForgetEnrichment.of (Complex R) (representable R x))) (x : D) (n : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (freeSphere R D x n) := by
  have h0 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (freeSphere R D x 0) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_iff_of_iso R D
      (moduleTensorUnitIso R D (representable R x))).mpr (hgen x)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_iff_of_iso R D
    (freeSphereShiftIso R D x 0 (-n) ≪≫ eqToIso
      (congrArg (freeSphere R D x) (by omega : 0 - -n = n)))).mp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_shift R D h0 (-n))

lemma dgKappaSphereFreeModule_isKappaCompact_of_generators
    (hgen : ∀ x : D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ
      (ForgetEnrichment.of (Complex R) (representable R x))) (i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D i) := by
  apply dgModuleKappaCompact_smallCoproduct R D hκ
  · apply (hasCardinalLT_iff_of_equiv (equivShrink.{u} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeCells D i)) κ).mpr
    exact (hasCardinalLT_iff_cardinal_mk_lt _ κ).mpr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeCells_card_lt D i)
  · intro j
    exact dgModuleKappaCompact_freeSphere R D hgen _ _

lemma dgKappaPerfectRepresentative_isKappaCompact_of_generators
    (hgen : ∀ x : D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ
      (ForgetEnrichment.of (Complex R) (representable R x)))
    (i : SmallModel.{u} (PerfectModuleCategoryOver R D Set.univ)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPerfectRepresentative R D i) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_of_perfectOver R D hκ Set.univ (fun x _ => hgen x)
    (perfectDGModuleRepresentative R D Set.univ i).property.2

lemma dgKappaClosedProjectiveObjects_isKappaCompact_of_generators
    (hgen : ∀ x : D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ
      (ForgetEnrichment.of (Complex R) (representable R x)))
    (M : ModuleCategory R D) (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_property R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_zero R D hκ.le)
    (fun M h s => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_shift R D h s)
    (fun M N hM hN => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_binary R D hκ hM hN)
    (fun M N hM hN f => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_cone R D hκ hM hN f)
    (fun M h => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_countableCoproduct R D hκ M h)
    (dgKappaSphereFreeModule_isKappaCompact_of_generators R D hκ hgen)
    (dgKappaPerfectRepresentative_isKappaCompact_of_generators R D hκ hgen) M hM

end SerrePositivity.InfinityCategories.Project.DerivedCategories
