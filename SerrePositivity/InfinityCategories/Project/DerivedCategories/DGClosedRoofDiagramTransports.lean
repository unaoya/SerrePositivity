module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRoofPrismComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoefficientFinitePairs

/-! # 閉細分に沿う一般図式の二輸送

概要：一般の部分係数と商図式を、追加閉分母から元の実分母へ全時刻を保って輸送する。
方針：全係数の元・商の細分 prism を引き戻し、厳密な係数境界で始端を揃える。
規約：標準単体の境界に制限しない。使われ方：一般有限対の実屋根充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet MonoidalCategory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {s' s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (R : s' ⟶ s)
variable {L K : SSet.{max u v}} (i : L ⟶ K)
variable (b : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
variable (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
variable (t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y)
variable (ht : i ≫ t = b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := y) R.hom.left)

include ht in
/-- 一般図式の充填境界を、元の実分母上の指定部分へ輸送する。 -/
def dgClosedRoofDiagramBoundaryTransport : SSet.Homotopy
    (i ≫ t ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s')
    (b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefinementHomotopy A D P x y R) b)
    (by simpa only [Category.assoc] using
      congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s') ht.symm) rfl

/-- 境界輸送の全時間の射は、指定部分で引き戻した同じ元 prism。 -/
lemma dgClosedRoofDiagramBoundaryTransport_h :
    (dgClosedRoofDiagramBoundaryTransport A D P x y R i b t ht).h =
      (b ▷ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefinementPrism A D P x y R :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyRetarget_h _ _ _

/-- 商全体の図式を、元の実分母へ輸送する。 -/
def dgQuotientRoofDiagramTransport : SSet.Homotopy
    (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map R.hom.left) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s')
    (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofRefinementHomotopy A D P x y R) g

/-- 厳密な係数正方形から、一般図式の二輸送の全境界・全時刻の一致を得る。 -/
lemma dgClosedRoofDiagramTransport_boundary
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) y) = i ≫ g) :
    (i ▷ Δ[1]) ≫ (dgQuotientRoofDiagramTransport A D P x y R g).h =
      (dgClosedRoofDiagramBoundaryTransport A D P x y R i b t ht).h ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y := by
  rw [dgClosedRoofDiagramBoundaryTransport_h]
  change (i ▷ Δ[1]) ≫ ((g ▷ Δ[1]) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofRefinementPrism A D P x y R) = _
  rw [← Category.assoc, ← comp_whiskerRight, ← hb, comp_whiskerRight,
    Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefinementPrism_comparison]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
