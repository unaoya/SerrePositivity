module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberRelativeRightComparison

public import SerrePositivity.KST.LocalizingInvariants.CofiberRelativeDiagramComparison
public import SerrePositivity.KST.LocalizingInvariants.ArrowFamilyHomNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.HomotopyIsoPostcomp

/-!
概要：同じ底辺の全 cofiber 図式比較は、指定右辺の自然性とその始点の恒等性を保つ。
方針：全図式比較を右辺へ制限し、底辺の恒等式を共通頂点へ評価する。
規約：関手圏全体の二胞体を扱う。使われ方：商の右辺と C 単位の同時比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
  {A : SSet.{u}} [Quasicategory A] (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.space X)
  (h : f ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X = g ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X)

lemma relativeComparison_right_naturality :
    homPost (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
        (relativeComparison X f g h).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom (g ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X) ≫
        homPost (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
          (relativeComparison X f g h).hom := by
  have he := arrowFamilyHom_naturality (f ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X) (g ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X)
    (homPost (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X) (relativeComparison X f g h).hom)
  rw [← homPost_comp, ← homPost_comp] at he
  exact he

omit [Quasicategory A] in
lemma relativeComparison_rightSource_arrow :
    Arrow.mk (homPost (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
        (relativeComparison X f g h).hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))) :
          hoFunctor.obj ((ihom A).obj X))) := by
  let F := (hoFunctor.map ((ihom A).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))).toFunctor
  have he := congrArg F.mapArrow.obj (relativeComparison_bottom_arrow X f g h)
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIso_postcomp_hom] at he
  change Arrow.mk (homPost (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (homPost (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X) (relativeComparison X f g h).hom)) = Arrow.mk (F.map (𝟙 _)) at he
  rw [CategoryTheory.Functor.map_id, ← homPost_comp] at he
  change Arrow.mk (homPost (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (relativeComparison X f g h).hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))) :
          hoFunctor.obj ((ihom A).obj X))) at he
  have hl := congrArg (fun k : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.space X ⟶ X =>
    Arrow.mk (homPost k (relativeComparison X f g h).hom)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.bottomTarget_eq_rightSource X)
  let I (k : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.space X ⟶ X) : Arrow (hoFunctor.obj ((ihom A).obj X)) :=
    Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ k))))
  have hr := congrArg I (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.bottomTarget_eq_rightSource X)
  exact hl.symm.trans (he.trans hr)

end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
