module
public import SerrePositivity.KST.NonConnective.DGKappaPerfectInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleKappaCompactClassicalTransport

/-!
概要：元の cone 内の頂点同型は、同じ主導来 perfect 集合の所属を保存する。
方針：実導来包含の像を元の主導来比較へ送り、perfect 性の同型不変性を使う。
規約：cone に同型コピーを追加しない。既存の集合を性質として比較する。
使われ方：K-7 e の Morita cone 同値の逆を、同じ実商の零化対象へ送る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ実 cone 内の指定頂点同型は、元の主導来加群の同型を誘導する。 -/
def dgKappaConeVertexIso_classicalIso {M N : DGKappaCone R D I}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D I))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)) :
    (moduleToDerived R D).obj M.val ≅ (moduleToDerived R D).obj N.val :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertex_classicalIso R D M.val).symm ≪≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedHoComparison R D).mapIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (dgKappaConeDerivedComparison R D I)) ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertex_classicalIso R D N.val

/-- 実 cone の同型頂点で、商の元の perfect 零化集合の所属は同値。 -/
theorem dgKappaConePerfectObjects_iff_of_vertexIso {M N : DGKappaCone R D I}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D I))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)) :
    M ∈ dgKappaConePerfectObjects R D I ↔ N ∈ dgKappaConePerfectObjects R D I := by
  have h := dgKappaConeVertexIso_classicalIso R D I e
  exact ⟨(modulePerfect R D).prop_of_iso h, (modulePerfect R D).prop_of_iso h.symm⟩

end SerrePositivity.KST.NonConnective
