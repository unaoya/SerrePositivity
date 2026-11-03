module
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeModules
public import SerrePositivity.InfinityCategories.Derived.DGModuleClosedPropertyStability
public import SerrePositivity.DifferentialGraded.Derived.Basic
/-!
概要：全 Hom end の意味で射影的な右 dg 加群の安定な実 nerve。
方針：零・cone・shift の実閉性から標準四角形を制限する。
規約：元の dg 圏の Hom の平坦性を仮定しない。使われ方：β5 の半自由模型との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 全 Hom end による射影的加群の実対象条件。 -/
def dgModuleProjectiveProperty (M : RightModule R D) : Prop :=
  moduleHomotopicallyProjective R D (ForgetEnrichment.of (Complex R) M)
/-- 射影的右 dg 加群の全 dg 部分圏。 -/
abbrev ProjectiveDGModules := DGFullSubcategory (RightModule R D) (dgModuleProjectiveProperty R D)
/-- 射影的右 dg 加群の実 dg nerve。 -/
abbrev dgProjectiveModuleNerve := dgNerve R (ProjectiveDGModules R D)
/-- 射影的加群は、零・標準 cone・標準 fiber で閉じる。 -/
lemma dgModuleProjectiveProperty_closed : DGModuleClosedProperty R D
    (dgModuleProjectiveProperty R D) where
  zero := moduleHomotopicallyProjective_of_isZero R D (moduleZero_isZero R D)
  cone f hM hN := moduleHomotopicallyProjective_cone R D hM hN f
  fiber f hM hN := moduleHomotopicallyProjective_shift R D
    (moduleHomotopicallyProjective_cone R D hM hN f) (-1)
/-- 全 Hom end による射影的加群の実 nerve は安定。 -/
theorem dgProjectiveModuleNerve_isStable : IsStable (dgProjectiveModuleNerve R D) :=
  dgClosedModule_isStable R D _ (dgModuleProjectiveProperty_closed R D)
/-- 射影的加群の実包含は完全。 -/
theorem dgProjectiveModuleInclusion_isExactFunctor : IsExactFunctor
    (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
      (dgModuleProjectiveProperty R D))) :=
  dgClosedModuleInclusion_isExactFunctor R D _ (dgModuleProjectiveProperty_closed R D)
/-- 半自由加群から射影的加群への、全 Hom end を保つ実 dg 包含。 -/
def dgSemifreeToProjective : DGFunctor R (SemifreeDGModules R D) (ProjectiveDGModules R D) where
  obj M := ⟨M.val, dgSemifreeModule_isProjective R D M⟩
  map _ _ := 𝟙 _
  map_id _ := by simp only [Category.comp_id]; rfl
  map_comp _ _ _ := by
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]
    rfl
/-- 半自由模型と射影的模型の比較は全写像空間で充満忠実。 -/
lemma dgSemifreeToProjectiveNerve_isFullyFaithful :
    IsFullyFaithful (dgNerve.map (dgSemifreeToProjective R D)) := by
  apply dgNerve_map_isFullyFaithful_of_homIso
  intro M N
  change IsIso (𝟙 (moduleHom R D M.val N.val))
  infer_instance
end SerrePositivity.InfinityCategories
