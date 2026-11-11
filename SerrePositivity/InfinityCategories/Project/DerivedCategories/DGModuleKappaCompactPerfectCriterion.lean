module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleKappaCompactBinary
public import SerrePositivity.DifferentialGraded.Perfect.Basic
/-!
概要：代表生成元の native κ-compact 性から有限 cell と実 perfect 加群の κ-compact 性を回収する。
方針：同じ有限操作木を帰納し、実導来 retract を native 頂点へ引き戻す。
規約：代表生成元の κ-compact 性は明示入力。ordinary compact 性へ置換しない。
使われ方：D-8 c2 の基底証明を c6 の実 perfect 代表へ接続する判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
variable {κ : Cardinal.{u}} [hreg : Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
include hreg hκ

lemma dgModuleKappaCompact_finiteCellOver (S : Set D)
    (hS : ∀ x ∈ S, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.representable R x)))
    {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} (hM : _root_.SerrePositivity.DifferentialGraded.moduleFiniteCellOver R D S M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M := by
  obtain ⟨c⟩ := hM
  induction c with
  | zero => exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_zero R D hκ.le
  | generator x hx => exact hS x hx
  | shift s c ih => exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_shift R D ih s
  | sum c d ihc ihd =>
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_iff_of_iso R D
      (_root_.SerrePositivity.DifferentialGraded.moduleBiprodIso R D _ _ ≪≫ biprod.isoCoprod _ _)).mpr
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_binary R D hκ ihc ihd)
  | cone c d f ihc ihd => exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_cone R D hκ ihc ihd f
  | iso c e ih => exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_iff_of_iso R D e).mp ih

lemma dgModuleKappaCompact_of_perfectOver (S : Set D)
    (hS : ∀ x ∈ S, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.representable R x)))
    {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} (hM : _root_.SerrePositivity.DifferentialGraded.modulePerfectOver R D S ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj M)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M := by
  obtain ⟨N, hN, ⟨r⟩⟩ := (_root_.SerrePositivity.DifferentialGraded.modulePerfectOver_iff R D S _).mp hM
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_of_derivedRetract R D r
    (dgModuleKappaCompact_finiteCellOver R D hκ S hS hN)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
