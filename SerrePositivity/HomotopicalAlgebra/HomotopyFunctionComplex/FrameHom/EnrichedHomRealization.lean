module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.EnrichedHomFunctor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.HomInfinityBifunctor

/-!
概要：元の豊穣 Hom 関手を小さい coherent nerve 全体で空間値に実現する。
方針：同じ豊穣関手を全単体で後合成し、通常の nerve の制限を全次数で照合する。
規約：宇宙持ち上げと元の全 Hom 作用を保持する。
使われ方：strict hammock Hom 図式から正本の共変 Hom 関手への全比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.SSet _root_.Opposite _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {D : Type u} [Category.{u} D] [SimplicialCategory D]
  [∀ A B : D, KanComplex (SimplicialCategory.sHom A B)] (X : D)

/-- 概要：同じ元の Hom 関手の coherent nerve 全体での実現。
方針：同じ合成作用を各 thickening 図式へ後合成する。
規約：同じ小さい coherent nerve の宇宙持ち上げ。
使われ方：Yoneda 側との全図式同型の始域。
-/
def enrichedHomCoherent : SSet.uliftFunctor.{u + 1, u}.obj (SimplicialNerve D) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} where
  app _ := ↾fun s => s.down.comp SSet (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomFunctor X)
  naturality _ _ _ := rfl

/-- 概要：元の Hom の全高次作用を忘れた同じ通常の Kan 図式。
方針：元の豊穣関手の通常の作用だけを取る。
規約：対象・元の射を選び直さない。
使われ方：strict な hammock Hom 図式の同定。
-/
def enrichedHomOrdinaryFamily : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomFunctor X)

/-- 概要：同じ通常の Hom 図式の射は元の豊穣後合成そのもの。
方針：豊穣単位からの射の同値と curry の自然性を使う。
規約：元の射の全次数の作用。使われ方：hammock Hom の通常射との厳密な照合。
-/
lemma enrichedHomOrdinaryFamily_map {Y Z : D} (f : Y ⟶ Z) :
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomOrdinaryFamily X).map f = eHomWhiskerLeft SSet X f := by
  have h : eHomEquiv SSet ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomOrdinaryFamily X).map f) =
      eHomEquiv SSet f ≫ curry (eComp SSet X Y Z) := by
    apply (SSet.unitHomEquiv _).injective
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomFunctor X) f
  apply (eHomEquiv SSet).injective
  rw [h]
  change (eHomEquiv SSet f) ≫ curry (eComp SSet X Y Z) =
    MonoidalClosed.curry' (eHomWhiskerLeft SSet X f)
  rw [← MonoidalClosed.curry_natural_left]
  change MonoidalClosed.curry _ = MonoidalClosed.curry
    ((ρ_ _).hom ≫ (ρ_ _).inv ≫
      _ ◁ eHomEquiv SSet f ≫ eComp SSet X Y Z)
  simp only [Iso.hom_inv_id_assoc]

/-- 概要：通常の nerve 上への制限は同じ strict Kan Hom 図式の実現そのもの。
方針：順序図式の豊穣後合成の原本を全単体で適用する。
規約：全次数での厳密な等式。
使われ方：点ごとの比較を用いない全図式の始端の照合。
-/
lemma enrichedHomCoherent_ordinary :
    SSet.uliftFunctor.{u + 1, u}.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent D) ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomCoherent X =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomOrdinaryFamily X) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram_postcomp _ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.enrichedHomFunctor X)

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
