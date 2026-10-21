module
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeProjectiveEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorExact
/-!
概要：半自由入力の周囲への実包含と、生の dg 関手への制限の完全性を示す。
方針：半自由・射影的模型の同値と射影的包含の完全性を合成する。
規約：生の出力の射影性は不要。使われ方：一般出力分解の Hom 試験の標的四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
omit [DGCategory R E] [Small.{u} E] in
/-- 同じ半自由入力の実包含と生の関手の完全性。 -/
lemma dgSemifreeToProjective_comp_inclusion :
    (dgSemifreeToProjective R D).comp
      (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)) =
      dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgSemifreeToProjective, dgFullSubcategoryInclusion,
    Category.comp_id, eqToHom_refl]
omit [DGCategory R E] [Small.{u} E] in
/-- 同じ半自由入力の実包含と生の関手の完全性。 -/
lemma dgSemifreeModulesInclusion_isExactFunctor :
    IsExactFunctor (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
      (dgModuleSemifreeProperty R D))) := by
  have h := congrArg (fun H => dgNerve.map H) (dgSemifreeToProjective_comp_inclusion R D)
  simp only [dgNerve.map_comp] at h
  rw [← h]
  let := isExactFunctor_of_isQCatEquivalence
    (dgSemifreeToProjectiveNerve_isQCatEquivalence R D)
  let := dgProjectiveModuleInclusion_isExactFunctor R D
  exact isExactFunctor_comp _ _
/-- 同じ半自由入力の実包含と生の関手の完全性。 -/
lemma dgSemifreeModuleFunctorRaw_isExactFunctor
    (F : DGFunctor R (RightModule R D) (RightModule R E)) :
    IsExactFunctor (dgNerve.map
      ((dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)).comp F)) := by
  rw [dgNerve.map_comp]
  let := dgSemifreeModulesInclusion_isExactFunctor R D
  let := dgModuleFunctorNerve_isExactFunctor R D E F
  exact isExactFunctor_comp _ _
end SerrePositivity.InfinityCategories
