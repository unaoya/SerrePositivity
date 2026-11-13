module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulatedYonedaExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGModuleExtensionYonedaNerveIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleFunctorExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGUniverseLiftFunctor

/-! # 共通宇宙の前三角 dg 関手の完全性

概要：前三角 dg 圏間の dg 関手の対象宇宙を上げた native nerve は完全。
方針：全加群への延長の完全性、Yoneda 比較の実関手同型、押し出しの反映を使う。
規約：全 cofiber 列の保存を証明。使われ方：元の宇宙の商関手の完全性への降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

omit [Small.{u} D] in
/-- 共通宇宙の関手と Yoneda の合成は、元の対象像の Yoneda と厳密に一致。 -/
lemma dgUniverseLiftFunctor_comp_yoneda :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, v, max (u + 1) v, max (u + 1) v} F).comp
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown A E).comp (dgYoneda A E)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown A D).comp (F.comp (dgYoneda A E)) := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex A) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown,
    _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation, Category.id_comp, Category.comp_id, eqToHom_refl]

/-- 加群値の対象像の Yoneda は、前三角始域において完全。 -/
lemma dgPretriangulatedFunctorYoneda_isExactFunctor [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
      (F.comp (_root_.SerrePositivity.DifferentialGraded.dgYoneda A E)))) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedYoneda_isExactFunctor A D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorNerve_isExactFunctor A D E (dgModuleExtension A D E F)
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_functorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionYonedaCompositeIso A D E F)

/-- 前三角 dg 圏間の dg 関手の共通宇宙の native nerve は完全。 -/
theorem dgPretriangulatedFunctorLifted_isExactFunctor
    [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, v, max (u + 1) v, max (u + 1) v} F)) where
  preservesZero := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_preservesZeroVertices _
  preservesCofiber t ht := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedYoneda_reflectsPushoutSquare A E
    have h := dgPretriangulatedFunctorYoneda_isExactFunctor A D E F
    rw [← dgUniverseLiftFunctor_comp_yoneda A D E F, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at h
    let := h
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber
      (F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, v, max (u + 1) v, max (u + 1) v} F) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown A E).comp (dgYoneda A E))) t ht
    simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ZeroTriangle.map, Category.assoc] using hc

end SerrePositivity.InfinityCategories.Project.DerivedCategories
