module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedHomStandardCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.AWClosedComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPostcompositionComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPostcompositionEquivalence

/-! # 全次元 AW 合成と実閉射の後合成

概要：実閉射の標準定数単体との AW 合成を、同じ実閉射による pinched 後合成に同定する。
方針：標準座標の単射性、定数 AW 成分計算、豊穣後合成の全次数成分式を使う。
規約：全次元で厳密な等式。使われ方：実屋根 Ore 合成の指定三角形との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 指定閉射を標準 DK 座標の定数単体として実 pinched Hom に移す。 -/
def pinchedClosedStandardSimplex {y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) _⦋n⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso y z).hom.app _
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s) n))

/-- 実閉定数単体の標準座標は、指定閉射の同じ標準定数。 -/
lemma pinchedClosedStandardSimplex_coordinates {y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) (n : ℕ) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso y z).inv.app _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedStandardSimplex A D s n)).down =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s) n :=
  congrArg ULift.down (ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso y z).hom_inv_id (Opposite.op ⦋n⦌)) _)

/-- 全次元 AW 合成に閉定数を後から適用すると、元の実 pinched 後合成に厳密に一致。 -/
lemma pinchedHomComposition_closed_post {x y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z)
    {n : ℕ} (f : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition x y z).app _ (f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedStandardSimplex A D s n) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition A D (x := x) s).app _ f := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomStandard_injective x z n
  dsimp only
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_standard x y z, pinchedClosedStandardSimplex_coordinates]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A D _ _ s) n).val
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x y).inv.app _ f).down).val).component J k hJ hk =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x z).inv.app _
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition A D (x := x) s)).app _ f)).down).val.component
          J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.awData_closed_post_component, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_standard_component,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition_f]

/-- 全次元 AW 合成に閉定数を先に適用すると、元の実 pinched 前合成に厳密に一致。 -/
lemma pinchedHomComposition_closed_pre [Small.{u} D] {x y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
    {n : ℕ} (g : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition x y z).app _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedStandardSimplex A D s n, g) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := z) s).app _ g := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomStandard_injective x z n
  dsimp only
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_standard x y z, pinchedClosedStandardSimplex_coordinates]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso y z).inv.app _ g).down).val
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A D _ _ s) n).val).component J k hJ hk =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x z).inv.app _
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D (y := z) s)).app _ g)).down).val.component
          J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.awData_closed_pre_component, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_standard_component,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_f]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
