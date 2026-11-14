module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.ResolutionComparisons.DeformationFunctorDescent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomotopyRawTransport
/-!
概要：指定降下比較の射を、元の実変形ホモトピーの通常後続像へ同定する。
方針：同じ点ごとの可逆像と円柱を保って端点輸送を比較する。
規約：別の同型やホモトピーを選ばない。使われ方：K-flat の指定比較の経路展開。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
/-- 元の降下比較の射は、同じ実変形ホモトピーの通常後続像の全関手射。 -/
lemma deformationFunctorDescentIso_hom_heq {X D Y : SSet.{u}} [Quasicategory Y]
    (L : X ⟶ D) (I : D ⟶ X) (W : Set (X _⦋1⦌))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge ∈ W)
    (T : X ⟶ Y) (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges T W) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso L I W H hH T hT).hom
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H T))) := by
  let H' := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H T
  have hi : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H' x).toTruncated := by
    intro x
    have h := hT (hH x)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := Y)
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H' x).toTruncated)
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge).map
        ((truncation 2).map T)) rfl).mpr h
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy H' hi
  have he : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso L I W H hH T hT) e := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso, Eq.mp]
    rfl
  have heh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso L I W H hH T hT) e
    (Category.assoc L I T).symm (Category.id_comp T).symm he
  exact heh

/-- 同じ実変形円柱を保ち、降下比較と同じ端点へ揃えたホモトピー。 -/
def deformationFunctorDescentHomotopy {X D Y : SSet.{u}}
    (L : X ⟶ D) (I : D ⟶ X) (H : SSet.Homotopy (L ≫ I) (𝟙 X)) (T : X ⟶ Y) :
    SSet.Homotopy (L ≫ I ≫ T) T := by
  let A := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H T
  exact { h := A.h
          h₀ := by simpa only [Category.assoc] using! A.h₀
          h₁ := by simpa only [Category.id_comp] using! A.h₁
          rel := A.rel }
/-- 元の指定降下比較の射を、同じ型の実ホモトピーの類へ厳密に回収する。 -/
lemma deformationFunctorDescentIso_hom {X D Y : SSet.{u}} [Quasicategory Y]
    (L : X ⟶ D) (I : D ⟶ X) (W : Set (X _⦋1⦌))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge ∈ W)
    (T : X ⟶ Y) (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges T W) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso L I W H hH T hT).hom =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (deformationFunctorDescentHomotopy L I H T)) := by
  have h1 := deformationFunctorDescentIso_hom_heq L I W H hH T hT
  have h2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopyHom_heq_of_raw_eq (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H T)
    (deformationFunctorDescentHomotopy L I H T) rfl
  exact eq_of_heq (h1.trans h2)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
