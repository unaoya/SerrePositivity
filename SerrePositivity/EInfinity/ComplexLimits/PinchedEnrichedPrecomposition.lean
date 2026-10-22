module

public import SerrePositivity.EInfinity.ComplexLimits.EnrichedPrecomposeComponents
public import SerrePositivity.InfinityCategories.Derived.DGClosedPostcompositionInterval

/-!
# 小ささ仮定なしの元の豊穣前合成と全区間族

概要：同じ閉射の全 Hom 前合成を、元の dg nerve 内の同じ射の前合成へ接続する。
方針：全次元 AW 合成の閉定数公式と元の全パラメータ族の合成判定を使う。
規約：対象圏の Small や任意の写像空間同値を入力にしない。
使われ方：全複体における実自由単位と同じ ∞ 前合成の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGNerve DGNerve.PinchedHom DoldKanComparison
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

def pinchedEnrichedPrecomposition {x y z : D}
    (s : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y) :
    DGNerve.pinchedHom A D y z ⟶ DGNerve.pinchedHom A D x z :=
  pinchedHomChainMap (D := D) (E := D) (x := y) (y := z) (x' := x) (y' := z)
    (eHomWhiskerRight (Complex A) s (ForgetEnrichment.of (Complex A) z))

lemma pinchedHomComposition_enriched_pre {x y z : D}
    (s : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    {n : ℕ} (g : (DGNerve.pinchedHom A D y z) _⦋n⦌) :
    (pinchedHomComposition x y z).app _ (pinchedClosedStandardSimplex A D s n, g) =
      (pinchedEnrichedPrecomposition A D (z := z) s).app _ g := by
  apply pinchedHomStandard_injective x z n
  dsimp only
  rw [pinchedHomComposition_standard x y z, pinchedClosedStandardSimplex_coordinates]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (awData (((standardHomPinchedIso y z).inv.app _ g).down).val
      (standardConstant (closedHomEquiv A D _ _ s) n).val).component J k hJ hk =
    (((standardHomPinchedIso x z).inv.app _
      ((pinchedHomChainMap (D := D) (E := D) (x := y) (y := z) (x' := x) (y' := z)
        (eHomWhiskerRight (Complex A) s
          (ForgetEnrichment.of (Complex A) z))).app _ g)).down).val.component
        J k hJ hk
  rw [awData_closed_pre_component, pinchedHomChainMap_standard_component]
  exact (eHomWhiskerRight_compose_f A D s k _).symm

lemma pinchedHomCompositionFamily_enriched_pre {K : SSet.{max u v}} {x y z : D}
    (s : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    (g : K ⟶ DGNerve.pinchedHom A D y z) :
    pinchedHomCompositionFamily (SSet.const (pinchedClosedVertex A D s)) g =
      g ≫ pinchedEnrichedPrecomposition A D (z := z) s := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  change (pinchedHomComposition x y z).app _
    ((SSet.const (X := K) (pinchedClosedVertex A D s)).app _ k, g.app _ k) = _
  rw [pinchedClosedStandardSimplex_const_app, pinchedHomComposition_enriched_pre]
  rfl

lemma pinchedEnrichedPrecomposition_family {K : SSet.{max u v}} {x y z : D}
    (s : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    (g : K ⟶ DGNerve.pinchedHom A D y z) :
    dgPinchedFamilyHom A D (g ≫ pinchedEnrichedPrecomposition A D (z := z) s) =
      constantFunctorHomMap K (Truncated.HomotopyCategory.homMk (dgClosedEdge A D s)) ≫
        dgPinchedFamilyHom A D g := by
  have h := dgPinchedFamilyHom_comp A D (SSet.const (pinchedClosedVertex A D s)) g
  rw [pinchedHomCompositionFamily_enriched_pre] at h
  have hc : dgPinchedFamilyHom A D (SSet.const (X := K) (pinchedClosedVertex A D s)) =
      constantFunctorHomMap K (Truncated.HomotopyCategory.homMk (dgClosedEdge A D s)) :=
    pinchedFamilyHom_const_vertex (K := K) (X := dgNerve A D) (pinchedClosedVertex A D s)
  rw [hc] at h
  exact h.symm

end SerrePositivity.EInfinity.ComplexLimits
