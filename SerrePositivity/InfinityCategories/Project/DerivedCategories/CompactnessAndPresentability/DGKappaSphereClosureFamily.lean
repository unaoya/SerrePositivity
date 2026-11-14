module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGProjectiveClosureFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaSphereFreeFamily

/-!
概要：B′ の sphere-free 基底だけを持つ実射影的閉包族を定義する。
方針：既存の一般閉包構成を使い、perfect 小模型の基底は追加しない。
規約：旧閉包族と旧 cone 入力は変更しない。全同型コピーを集合へ追加しない。
使われ方：D-1 の telescope 被覆と D-2 の新 cone 入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- B′ の基底は κ-small sphere-free 加群だけ。 -/
def dgKappaSphereClosureBaseFamily (κ : Cardinal.{u}) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ,
    fun i ↦ ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D i, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule_projective R D i⟩⟩

/-- 同じ実和・shift・全閉零次射の cone で閉じた B′ の族。 -/
def dgKappaSphereClosureFamily (κ : Cardinal.{u}) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureFamily R D (T := κ.ord.ToType) (dgKappaSphereClosureBaseFamily R D κ)

/-- 同じ実加群の像集合。 -/
def dgKappaSphereClosureObjects (κ : Cardinal.{u}) : Set (ModuleCategory R D) :=
  Set.range (fun i ↦ ((dgKappaSphereClosureFamily R D κ).2 i).val)

lemma dgKappaSphereClosureObjects_small (κ : Cardinal.{u}) :
    Small.{u} {M : ModuleCategory R D // dgKappaSphereClosureObjects R D κ M} := small_range _

lemma dgKappaSphereClosureObjects_projective (κ : Cardinal.{u})
    (M : ModuleCategory R D) (hM : dgKappaSphereClosureObjects R D κ M) :
    moduleHomotopicallyProjective R D M := by
  obtain ⟨i, rfl⟩ := hM
  exact ((dgKappaSphereClosureFamily R D κ).2 i).property

end SerrePositivity.InfinityCategories.Project.DerivedCategories
