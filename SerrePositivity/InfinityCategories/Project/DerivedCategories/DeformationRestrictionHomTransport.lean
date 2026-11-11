module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DeformationFunctorDescentHom
/-!
概要：同じ制限比較と変形円柱の二段経路を、等しい通常後続関手へ移す。
方針：端点等式と指定同型の HEq を消去し、元の経路等式を保持する。
規約：新しい比較を選ばない。使われ方：K-flat 比較の射の標準化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
/-- 同じ制限比較と変形円柱の経路は、通常後続関手の端点輸送と整合する。 -/
lemma deformationRestrictionComparison_hom_heq {X D Y : SSet.{u}} [Quasicategory Y]
    (L : X ⟶ D) (I : D ⟶ X) (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    {K : D ⟶ Y} {T T' : X ⟶ Y} (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K (I ≫ T))
    (r' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K (I ≫ T')) (A : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ K) T)
    (ht : T = T') (hr : HEq r r')
    (hA : A.hom = (r.precomp L).hom ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H T))) :
    HEq A.hom ((r'.precomp L).hom ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H T'))) := by
  subst T'
  cases eq_of_heq hr
  exact heq_of_eq hA
end SerrePositivity.InfinityCategories.Project.DerivedCategories
