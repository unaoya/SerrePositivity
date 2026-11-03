module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationHomotopyNaturality
public import SerrePositivity.InfinityCategories.DGNerve.ClosedComposition
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 同じ実 augmentation と元の主導来像の比較。 -/
lemma dgModuleAugmentation_onHomotopy_naturality
    (X Y : DGModuleFunctorResolutionObject R C E F)
    (f : ForgetEnrichment.of (Complex R) X ⟶ ForgetEnrichment.of (Complex R) Y) :
    (moduleToHomotopy R E).map
      ((dgModuleAugmentationSource R C E F).onClosed.map f ≫ Y.augmentation) =
    (moduleToHomotopy R E).map
      (X.augmentation ≫ (dgModuleAugmentationTarget R C E F).onClosed.map f) := by
  apply (toHomotopy_map_eq_iff_boundary R (RightModule R E) _ _).2
  let a := closedHomEquiv R (DGModuleFunctorResolutionObject R C E F) _ _ f
  refine ⟨dgModuleAugmentationHomotopyComponent R C E F X Y 0 a.val, ?_⟩
  change differential R (x := X.replacement.val) (y := F.obj Y.source)
    (dgModuleAugmentationHomotopyComponent R C E F X Y 0 a.val) = _
  change _ =
    (closedHomEquiv R (RightModule R E)
      (ForgetEnrichment.of (Complex R) X.replacement.val)
      (ForgetEnrichment.of (Complex R) (F.obj Y.source))
      ((dgModuleAugmentationSource R C E F).onClosed.map f ≫ Y.augmentation)).val -
    (closedHomEquiv R (RightModule R E)
      (ForgetEnrichment.of (Complex R) X.replacement.val)
      (ForgetEnrichment.of (Complex R) (F.obj Y.source))
      (X.augmentation ≫ (dgModuleAugmentationTarget R C E F).onClosed.map f)).val
  rw [HomotopyComparison.closedHom_comp, HomotopyComparison.closedHom_comp]
  erw [DGFunctor.closedHomEquiv_map, DGFunctor.closedHomEquiv_map]
  exact dgModuleAugmentationHomotopyComponent_closed_zero R C E F X Y a.val a.property

/-- 同じ実 augmentation と元の主導来像の比較。 -/
def dgModuleAugmentation_onClosedToHomotopy :
    (dgModuleAugmentationSource R C E F).onClosed ⋙ moduleToHomotopy R E ⟶
      (dgModuleAugmentationTarget R C E F).onClosed ⋙ moduleToHomotopy R E where
  app X := (moduleToHomotopy R E).map (ForgetEnrichment.to (Complex R) X).augmentation
  naturality {X Y} f := by
    change (moduleToHomotopy R E).map ((dgModuleAugmentationSource R C E F).onClosed.map f) ≫
        (moduleToHomotopy R E).map (ForgetEnrichment.to (Complex R) Y).augmentation =
      (moduleToHomotopy R E).map (ForgetEnrichment.to (Complex R) X).augmentation ≫
        (moduleToHomotopy R E).map ((dgModuleAugmentationTarget R C E F).onClosed.map f)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact dgModuleAugmentation_onHomotopy_naturality R C E F _ _ f
/-- 同じ実 augmentation と元の主導来像の比較。 -/
def dgModuleAugmentation_onHomotopy :
    (dgModuleAugmentationSource R C E F).onHomotopy ⟶
      (dgModuleAugmentationTarget R C E F).onHomotopy := by
  refine CategoryTheory.Quotient.natTransLift
    (boundaryRelation R (DGModuleFunctorResolutionObject R C E F)) ?_
  change toHomotopy R (DGModuleFunctorResolutionObject R C E F) ⋙
      (dgModuleAugmentationSource R C E F).onHomotopy ⟶
    toHomotopy R (DGModuleFunctorResolutionObject R C E F) ⋙
      (dgModuleAugmentationTarget R C E F).onHomotopy
  rw [DGFunctor.onHomotopy_fac, DGFunctor.onHomotopy_fac]
  exact dgModuleAugmentation_onClosedToHomotopy R C E F

end SerrePositivity.InfinityCategories
