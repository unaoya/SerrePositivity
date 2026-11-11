module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofFunctorCorrespondence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.PinchedFamilyComposition
/-!
概要：実屋根の標的頂点の等式に沿う輸送を、両射影付きの厳密な同型として与える。
方針：等式の帰納法を使い、slice と pullback の輸送を照合する。
規約：対象の同値による輸送とは区別する。使われ方：商の標準頂点表示との比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
/-- 屋根の標的頂点の等式に沿う厳密な同型。 -/
def roofEndpointIso {I X : SSet.{u}} (s : I ⟶ X) {y y' : X _⦋0⦌} (h : y = y') :
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) s ≅
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y')) s :=
  eqToIso (congrArg (fun z => pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z)) s) h)
/-- 屋根の標的の輸送は、実 slice の同じ等式輸送を第一成分として持つ。 -/
lemma roofEndpointIso_fst {I X : SSet.{u}} (s : I ⟶ X) {y y' : X _⦋0⦌} (h : y = y') :
    (roofEndpointIso s h).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (eqToIso (congrArg
        (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) h)).hom := by
  subst y'
  simp [roofEndpointIso]
/-- 屋根の標的の輸送は、実添字を厳密に固定する。 -/
lemma roofEndpointIso_snd {I X : SSet.{u}} (s : I ⟶ X) {y y' : X _⦋0⦌} (h : y = y') :
    (roofEndpointIso s h).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  subst y'
  simp [roofEndpointIso]
/-- pinched Hom の端点の輸送と実 slice への包含は、同じ標的の輸送に一致する。 -/
lemma pinchedFamilySlice_endpointTransport {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice X x y ≫ (eqToIso (congrArg
      (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) hy)).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso hx hy).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice X x' y' := by
  subst x'
  subst y'
  simp [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso]
/-- 関手による標的 slice 写像の後の頂点輸送は、同じ点図式の等式による輸送に一致する。 -/
lemma roofTargetSliceMap_endpointTransport {X Y : SSet.{u}} (F : X ⟶ Y)
    (y : X _⦋0⦌) {z : Y _⦋0⦌} (hy : F.app (Opposite.op ⦋0⦌) y = z)
    (hp : SSet.yonedaEquiv.symm y ≫ F = SSet.yonedaEquiv.symm z) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap F y ≫ (eqToIso (congrArg
      (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) hy)).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (SSet.yonedaEquiv.symm y) F ≫
      (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver hp)).hom := by
  subst z
  simp only [eqToIso_refl]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
