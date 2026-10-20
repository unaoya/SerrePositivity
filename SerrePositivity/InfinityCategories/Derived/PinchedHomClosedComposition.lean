module
public import SerrePositivity.InfinityCategories.Derived.PinchedHomStandardCoordinates
public import SerrePositivity.InfinityCategories.Derived.AWClosedComposition
public import SerrePositivity.InfinityCategories.Derived.DGClosedPostcompositionComponents
public import SerrePositivity.InfinityCategories.Derived.DGClosedPostcompositionEquivalence

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve.PinchedHom DoldKanComparison
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 指定閉射を標準 DK 座標の定数単体として実 pinched Hom に移す。 -/
def pinchedClosedStandardSimplex {y z : D}
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z) (n : ℕ) :
    (DGNerve.pinchedHom A D y z) _⦋n⦌ :=
  (standardHomPinchedIso y z).hom.app _
    (ULift.up (standardConstant (closedHomEquiv A D _ _ s) n))

/-- 実閉定数単体の標準座標は、指定閉射の同じ標準定数。 -/
lemma pinchedClosedStandardSimplex_coordinates {y z : D}
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z) (n : ℕ) :
    ((standardHomPinchedIso y z).inv.app _ (pinchedClosedStandardSimplex A D s n)).down =
      standardConstant (closedHomEquiv A D _ _ s) n :=
  congrArg ULift.down (ConcreteCategory.congr_hom
    (NatTrans.congr_app (standardHomPinchedIso y z).hom_inv_id (Opposite.op ⦋n⦌)) _)

/-- 全次元 AW 合成に閉定数を後から適用すると、元の実 pinched 後合成に厳密に一致。 -/
lemma pinchedHomComposition_closed_post {x y z : D}
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z)
    {n : ℕ} (f : (DGNerve.pinchedHom A D x y) _⦋n⦌) :
    (pinchedHomComposition x y z).app _ (f, pinchedClosedStandardSimplex A D s n) =
      (pinchedClosedPostcomposition A D (x := x) s).app _ f := by
  apply pinchedHomStandard_injective x z n
  dsimp only
  rw [pinchedHomComposition_standard x y z, pinchedClosedStandardSimplex_coordinates]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (awData (standardConstant (closedHomEquiv A D _ _ s) n).val
    (((standardHomPinchedIso x y).inv.app _ f).down).val).component J k hJ hk =
      (((standardHomPinchedIso x z).inv.app _
        ((pinchedHomChainMap (dgClosedPostcomposition A D (x := x) s)).app _ f)).down).val.component
          J k hJ hk
  rw [awData_closed_post_component, pinchedHomChainMap_standard_component,
    dgClosedPostcomposition_f]

/-- 全次元 AW 合成に閉定数を先に適用すると、元の実 pinched 前合成に厳密に一致。 -/
lemma pinchedHomComposition_closed_pre [Small.{u} D] {x y z : D}
    (s : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    {n : ℕ} (g : (DGNerve.pinchedHom A D y z) _⦋n⦌) :
    (pinchedHomComposition x y z).app _ (pinchedClosedStandardSimplex A D s n, g) =
      (pinchedClosedPrecomposition A D (y := z) s).app _ g := by
  apply pinchedHomStandard_injective x z n
  dsimp only
  rw [pinchedHomComposition_standard x y z, pinchedClosedStandardSimplex_coordinates]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (awData (((standardHomPinchedIso y z).inv.app _ g).down).val
    (standardConstant (closedHomEquiv A D _ _ s) n).val).component J k hJ hk =
      (((standardHomPinchedIso x z).inv.app _
        ((pinchedHomChainMap (dgClosedPrecomposition A D (y := z) s)).app _ g)).down).val.component
          J k hJ hk
  rw [awData_closed_pre_component, pinchedHomChainMap_standard_component,
    dgClosedPrecomposition_f]
  rfl

end SerrePositivity.InfinityCategories
