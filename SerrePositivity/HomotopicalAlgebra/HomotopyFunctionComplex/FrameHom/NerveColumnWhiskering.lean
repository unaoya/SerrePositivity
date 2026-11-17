module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumnRoofNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.NerveTransformationInversion
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyComponent
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom

/-!
概要：元の通常変換と列の全同型の前合成・表示変更の法則。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalClosed _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
open _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom

/-- 同じ通常変換の全同型の順射は、元の列の全変換の類。 -/
lemma sameNerveTransformationPostIso_column
    {I C : Type u} [Category.{u} I] [Category.{u} C]
    {F G : I ⥤ C} (η : F ⟶ G) {Q : SSet.{u}} [Quasicategory Q]
    (L : nerve C ⟶ Q)
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated) :
    (nerveTransformationPostIso η L hη).hom = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom L η := by
  rw [nerveTransformationPostIso_hom]
  have he : nerveTransformationPostHomotopy η L =
      Homotopy.functorHomotopyPostcomp (nerveNatTransHomotopy η) L := rfl
  rw [he, Homotopy.functorHomotopyPostcomp_hom]
  exact congrArg (fun α => (hoFunctor.map ((ihom (nerve I)).map L)).toFunctor.map α)
    (nerveNatTransHomotopy_hom η)

/-- 通常列の全変換の類は、同じ添字関手による前合成と可換。 -/
lemma sameNerveColumn_whiskerLeft
    {I J C : Type u} [Category.{u} I] [Category.{u} J] [Category.{u} C]
    (R : J ⥤ I) {F G : I ⥤ C} (η : F ⟶ G)
    {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q) :
    (hoFunctor.map ((MonoidalClosed.pre (nerveMap R)).app Q)).toFunctor.map
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom L η) = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom L (CategoryTheory.Functor.whiskerLeft R η) := by
  have h :
      (hoFunctor.map ((ihom (nerve I)).map L)).toFunctor ⋙
        (hoFunctor.map ((MonoidalClosed.pre (nerveMap R)).app Q)).toFunctor =
      (hoFunctor.map ((MonoidalClosed.pre (nerveMap R)).app (nerve C))).toFunctor ⋙
        (hoFunctor.map ((ihom (nerve J)).map L)).toFunctor := by
    change (hoFunctor.map ((ihom (nerve I)).map L) ≫
      hoFunctor.map ((MonoidalClosed.pre (nerveMap R)).app Q)).toFunctor = _
    rw [← CategoryTheory.Functor.map_comp,
      (MonoidalClosed.pre (nerveMap R)).naturality L, CategoryTheory.Functor.map_comp]
    rfl
  have hh := CategoryTheory.Functor.congr_hom h (nerveNatTransHom η)
  simp only [CategoryTheory.Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] at hh
  unfold _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom
  rw [← nerveNatTransHom_whiskerLeft R η]
  exact hh

/-- 元の通常変換の全同型を制限すると、同じ制限変換から作った全同型になる。 -/
lemma sameNerveTransformationPostIso_precomp
    {I J C : Type u} [Category.{u} I] [Category.{u} J] [Category.{u} C]
    (R : J ⥤ I) {F G : I ⥤ C} (η : F ⟶ G)
    {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q)
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated) :
    HEq ((nerveTransformationPostIso η L hη).precomp (nerveMap R))
      (nerveTransformationPostIso (CategoryTheory.Functor.whiskerLeft R η) L
        (fun j => hη (R.obj j))) := by
  apply heq_of_eq
  apply Iso.ext
  rw [SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom]
  change (hoFunctor.map ((MonoidalClosed.pre (nerveMap R)).app Q)).toFunctor.map
    (nerveTransformationPostIso η L hη).hom = _
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sameNerveTransformationPostIso_column, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sameNerveTransformationPostIso_column]
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sameNerveColumn_whiskerLeft R η L

/-- 元の変換の端点と値の照合は、同じ関手へ送った全同型の値を保つ。 -/
lemma sameNerveTransformationPostIso_heq
    {I C : Type u} [Category.{u} I] [Category.{u} C]
    {F G F' G' : I ⥤ C} (hF : F = F') (hG : G = G')
    (η : F ⟶ G) (η' : F' ⟶ G') (he : HEq η η')
    {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q)
    (hη : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η.app i)).map L).toTruncated)
    (hη' : ∀ i, IsInvertibleEdge ((nerve.edgeMk (η'.app i)).map L).toTruncated) :
    HEq (nerveTransformationPostIso η L hη) (nerveTransformationPostIso η' L hη') := by
  subst F'
  subst G'
  cases eq_of_heq he
  rfl

/-- 同じ増大変換の全同型は、元の列の増大同型そのもの。 -/
lemma sameNerveTransformationPostIso_augmentation
    {I C : Type u} [Category.{u} I] [Category.{u} C]
    (V : I ⥤ C) {X : C} (p : V ⟶ (CategoryTheory.Functor.const I).obj X)
    {Q : SSet.{u}} [Quasicategory Q] (L : nerve C ⟶ Q)
    (hp : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map L).toTruncated) :
    nerveTransformationPostIso p L hp = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso L V p hp := by
  apply Iso.ext
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sameNerveTransformationPostIso_column, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso_hom]

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
