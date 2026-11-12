module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullSquareComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullTriangleShortComparisons

/-!
概要：元全核四角形比較の上下二胞体への制限は、既存の指定全三角形比較そのもの。
方針：同じ元ホモトピーの厳密な制限を、代表修正で保った全射の類へ移す。
規約：新しい三角形比較を選び直さず、元指定同型の等号を保持する。
使われ方：元全四角形比較の指定三境界の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma nullSquareWholeTriangle
    {f g : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}}
    {f' g' : (Δ[2] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}}
    (H : SSet.Homotopy f g) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (he : e.hom = Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))
    (q : (Δ[2] : SSet.{u + 2}) ⟶ Δ[1] ⊗ Δ[1]) (hf : q ≫ f = f') (hg : q ≫ g = g')
    (H' : SSet.Homotopy f' g') (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g')
    (he' : e'.hom = Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H'))
    (hh : (q ▷ (Δ[1] : SSet.{u + 2})) ≫ H.h = H'.h) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e.precomp q) hf hg = e' := by
  subst f' g'
  change e.precomp q = e'
  apply Iso.ext
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom, he, he']
  change Truncated.HomotopyCategory.homMk
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map
      ((truncation 2).map ((pre q).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}))) =
        Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H')
  apply congrArg Truncated.HomotopyCategory.homMk
  apply Truncated.Edge.ext
  change ((pre q).app _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1}).app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (curry H.h)) = SSet.yonedaEquiv (curry H'.h)
  rw [← SSet.yonedaEquiv_comp, curry_pre_app, hh]

variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元全核面比較の上三角形制限は元上全比較そのもの。
方針：元上二胞体と実全ホモトピーの厳密回収を同じ関手圏へ写す。
規約：指定全同型の等号。使われ方：元零角の指定境界の回収。 -/
lemma dgOdotMilnorNuNullSquareComparison_upper :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((dgOdotMilnorNuNullSquareComparison R d h).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0))
      (Equiv.symm_apply_apply SSet.yonedaEquiv
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)).symm
      (Equiv.symm_apply_apply SSet.yonedaEquiv
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))).symm =
      dgOdotMilnorNuNullUpperTriangleComparison R d h := by
  exact nullSquareWholeTriangle (dgOdotMilnorNuNullSquareHomotopy R d h)
    (dgOdotMilnorNuNullSquareComparison R d h) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0) _ _
    (dgOdotMilnorNuNullUpperTriangleHomotopy R d h)
    (dgOdotMilnorNuNullUpperTriangleComparison R d h) rfl
    (dgOdotMilnorNuNullSquareHomotopy_upper R d h)

/-- 概要：元全核面比較の下三角形制限は元下全比較そのもの。
方針：同じ共有対角への代表修正で保った元全比較の類を回収する。
規約：指定全同型の等号。使われ方：元包含辺と商辺の指定境界の回収。 -/
lemma dgOdotMilnorNuNullSquareComparison_lower :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((dgOdotMilnorNuNullSquareComparison R d h).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1))
      (Equiv.symm_apply_apply SSet.yonedaEquiv
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgOdotMilnorPerfectNullSquare R d ≫ dgKInputNu R)).symm
      (Equiv.symm_apply_apply SSet.yonedaEquiv
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h))).symm =
      dgOdotMilnorNuNullLowerTriangleComparison R d h := by
  exact nullSquareWholeTriangle (dgOdotMilnorNuNullSquareHomotopy R d h)
    (dgOdotMilnorNuNullSquareComparison R d h) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1) _ _
    (dgOdotMilnorNuNullAlignedLowerTriangleHomotopy R d h)
    (dgOdotMilnorNuNullLowerTriangleComparison R d h)
    (dgOdotMilnorNuNullAlignedLowerTriangleHomotopy_class R d h).symm
    (dgOdotMilnorNuNullSquareHomotopy_lower R d h)

end SerrePositivity.KST.SConstruction
