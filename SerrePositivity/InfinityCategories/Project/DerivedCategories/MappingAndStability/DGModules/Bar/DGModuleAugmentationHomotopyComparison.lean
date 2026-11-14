module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationHomotopyNaturality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ClosedComposition
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
/-!
概要：元の出力分解の augmentation を、閉射と実 H⁰ 関手の自然変換として比較する。
方針：元の比較 cochain の境界式と同じ指定局所化を使う。
規約：入力の Small 性・元の出力の射影性を仮定しない。使われ方：一般 kernel の Morita 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 同じ実 augmentation と元の主導来像の比較。 -/
lemma dgModuleAugmentation_onHomotopy_naturality
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) Y) :
    (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R E).map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).onClosed.map f ≫ Y.augmentation) =
    (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R E).map
      (X.augmentation ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).onClosed.map f) := by
  apply (_root_.SerrePositivity.DifferentialGraded.toHomotopy_map_eq_iff_boundary R (_root_.SerrePositivity.DifferentialGraded.RightModule R E) _ _).2
  let a := closedHomEquiv R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) _ _ f
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F X Y 0 a.val, ?_⟩
  change _root_.SerrePositivity.DifferentialGraded.differential R (x := X.replacement.val) (y := F.obj Y.source)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F X Y 0 a.val) = _
  change _ =
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R E)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X.replacement.val)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj Y.source))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).onClosed.map f ≫ Y.augmentation)).val -
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R (_root_.SerrePositivity.DifferentialGraded.RightModule R E)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X.replacement.val)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj Y.source))
      (X.augmentation ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).onClosed.map f)).val
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp]
  erw [_root_.SerrePositivity.DifferentialGraded.DGFunctor.closedHomEquiv_map, _root_.SerrePositivity.DifferentialGraded.DGFunctor.closedHomEquiv_map]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent_closed_zero R C E F X Y a.val a.property

/-- 同じ実 augmentation と元の主導来像の比較。 -/
def dgModuleAugmentation_onClosedToHomotopy :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).onClosed ⋙ moduleToHomotopy R E ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).onClosed ⋙ moduleToHomotopy R E where
  app X := (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R E).map (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) X).augmentation
  naturality {X Y} f := by
    change (moduleToHomotopy R E).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).onClosed.map f) ≫
        (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R E).map (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) Y).augmentation =
      (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R E).map (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) X).augmentation ≫
        (moduleToHomotopy R E).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).onClosed.map f)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact dgModuleAugmentation_onHomotopy_naturality R C E F _ _ f
/-- 同じ実 augmentation と元の主導来像の比較。 -/
def dgModuleAugmentation_onHomotopy :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).onHomotopy ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).onHomotopy := by
  refine CategoryTheory.Quotient.natTransLift
    (boundaryRelation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)) ?_
  change toHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) ⋙
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).onHomotopy ⟶
    toHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) ⋙
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).onHomotopy
  rw [_root_.SerrePositivity.DifferentialGraded.DGFunctor.onHomotopy_fac, _root_.SerrePositivity.DifferentialGraded.DGFunctor.onHomotopy_fac]
  exact dgModuleAugmentation_onClosedToHomotopy R C E F

end SerrePositivity.InfinityCategories.Project.DerivedCategories
