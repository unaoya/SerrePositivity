module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleDerivedFunctor
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  (hF : ∀ M, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D M → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E (F.obj M))
/-- 既存の実導来関手の半自由包含像は、元の同じ dg 関手と全関手同型で比較される。 -/
def dgModuleDerivedFunctor_underlyingIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor R D E F hF ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((dgFullSubcategoryInclusion R (RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)).comp F)) := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)
  let J := dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)
  let K := dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E)
  have h1 : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective R E).comp K = J := by
    apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
    intro x y
    simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective,
      eqToHom_refl, Category.comp_id]
  have h2 : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective R D).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF)).comp K = I.comp F := by
    apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
    intro x y
    simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullFunctorRestriction, eqToHom_refl,
      Category.comp_id, Category.id_comp]
  have e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor_comparisonIso R D E F hF).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map K)
  have hn1 := congrArg (fun H => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H) h1
  have hn2 := congrArg (fun H => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H) h2
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc] at hn1 hn2
  simp only [Category.assoc] at e
  rw [hn1, hn2] at e
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using e
end SerrePositivity.InfinityCategories.Project.DerivedCategories
