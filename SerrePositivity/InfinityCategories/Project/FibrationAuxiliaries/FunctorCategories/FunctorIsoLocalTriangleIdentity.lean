module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoTriangleCancellation
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoSquareIdentity
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra

/-!
概要：指定輸送三角形と制限正方形を貼り、局所比較の三辺の等式を回収する。
方針：第二辺の二因子の後合成を分配し、指定された逆因子を消去する。
規約：元の指定値を保持する。
使われ方：元の全 Hom 上の局所自然性の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 指定された局所比較の二辺に大域自然性を貼ると、直接の大域自然性になる。 -/
def FunctorIsoLocalTriangleCommutes {X Y : SSet.{u}} {a b c t : X ⟶ Y}
    (V : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (W : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b c)
    (K : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c t) (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a t) : Prop := V ≪≫ W ≪≫ K = D

/-- 同じ指定二因子を後合成して得た三角形から、局所比較の三角等式を回収する。 -/
lemma functorIsoLocalTriangle_of_postcomp_and_source_pasting
    {X Y Z : SSet.{u}} {a c d : X ⟶ Y} {b e e' t : X ⟶ Z}
    (p : Y ⟶ Z) (N : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a c) (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c d)
    (E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (a ≫ p) b) (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b t)
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso e (d ≫ p)) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d ≫ p) t)
    (K : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso e' t) (he : e = e')
    (hT : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoSquareCommutes E D (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (N ≪≫ L) p) F)
    (hR : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoPastingSourceIdentity R F K he) :
    FunctorIsoLocalTriangleCommutes (E.symm ≪≫ N.postcomp p)
      (L.postcomp p ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq R he rfl).symm) K D := by
  have ht : E ≪≫ D = (N.postcomp p ≪≫ L.postcomp p) ≪≫ F := by
    exact Eq.trans hT (congrArg (fun i ↦ i ≪≫ F) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans N L p))
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_localTriangle_of_transport_and_restriction E (N.postcomp p)
    (L.postcomp p) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq R he rfl) F K D ht hR

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
