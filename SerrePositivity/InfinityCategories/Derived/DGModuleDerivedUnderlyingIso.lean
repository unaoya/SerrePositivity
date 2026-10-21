module
public import SerrePositivity.InfinityCategories.Derived.DGModuleDerivedFunctor
/-!
概要：既存の射影的模型による実導来関手を、元の dg 関手の生の包含像へ比較する。
方針：同じ射影的比較の余単位へ実包含を後合成し、厳密な dg 等式を照合する。
規約：全関手同型で元の関手を保持する。使われ方：実出力分解との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  (F : DGFunctor R (RightModule R D) (RightModule R E))
  (hF : ∀ M, dgModuleProjectiveProperty R D M → dgModuleProjectiveProperty R E (F.obj M))
/-- 既存の実導来関手の半自由包含像は、元の同じ dg 関手と全関手同型で比較される。 -/
def dgModuleDerivedFunctor_underlyingIso :
    FunctorIso (dgModuleDerivedFunctor R D E F hF ≫ dgNerve.map
      (dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)))
      (dgNerve.map ((dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)).comp F)) := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)
  let J := dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)
  let K := dgFullSubcategoryInclusion R (RightModule R E) (dgModuleProjectiveProperty R E)
  have h1 : (dgSemifreeToProjective R E).comp K = J := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro x y
    simp only [EnrichedFunctor.comp_map, dgSemifreeToProjective,
      eqToHom_refl, Category.comp_id]
  have h2 : ((dgSemifreeToProjective R D).comp
      (dgProjectiveModuleFunctor R D E F hF)).comp K = I.comp F := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro x y
    simp only [EnrichedFunctor.comp_map, dgSemifreeToProjective,
      dgProjectiveModuleFunctor, dgFullFunctorRestriction, eqToHom_refl,
      Category.comp_id, Category.id_comp]
  have e := (dgModuleDerivedFunctor_comparisonIso R D E F hF).postcomp (dgNerve.map K)
  have hn1 := congrArg (fun H => dgNerve.map H) h1
  have hn2 := congrArg (fun H => dgNerve.map H) h2
  simp only [dgNerve.map_comp, Category.assoc] at hn1 hn2
  simp only [Category.assoc] at e
  rw [hn1, hn2] at e
  simpa only [dgNerve.map_comp] using e
end SerrePositivity.InfinityCategories
