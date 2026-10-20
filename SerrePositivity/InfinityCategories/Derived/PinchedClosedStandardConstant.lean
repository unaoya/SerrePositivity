module
public import SerrePositivity.InfinityCategories.Derived.PinchedHomClosedComposition
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedVertexNaturality

/-! # 元の実閉辺の定数族と AW 前後合成

概要：標準閉定数を元の実閉辺の pinched 頂点の定数族と同定する。
方針：零次元の閉元と標準座標を比較し、同型の自然性で全次元へ移す。
規約：実閉辺と有限パラメータ族を選び直さない。使われ方：実 Ore ホモトピーとの接続。
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
/-- 標準 DK 座標で作った閉定数の頂点は、元の指定閉辺の pinched 頂点。 -/
lemma pinchedClosedStandardSimplex_zero {x y : D}
    (s : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y) :
    pinchedClosedStandardSimplex A D s 0 = pinchedClosedVertex A D s := by
  apply pinchedHomStandard_injective x y 0
  dsimp only
  rw [pinchedClosedStandardSimplex_coordinates, pinchedHomStandard_coordinates]
  apply (standardZeroEquiv x y).injective
  apply Subtype.ext
  change (standardConstant (closedHomEquiv A D _ _ s) 0).val.component
    Finset.univ 0 Finset.univ_nonempty (by decide) =
      (signChangeData (toLinearSimplex (pinchedClosedVertex A D s)).val).component
        Finset.univ 0 Finset.univ_nonempty (by decide)
  rw [signChangeData_component]
  change (standardConstant (closedHomEquiv A D _ _ s) 0).val.component
    Finset.univ 0 Finset.univ_nonempty (by decide) =
      (1 : ℤ) • pinchedLinearVertexValue (toLinearSimplex (pinchedClosedVertex A D s))
  rw [one_smul, pinchedClosedVertex_linearValue]
  simpa only [show (Finset.univ : Finset (Fin 1)) = {0} from by decide] using
    standardConstant_singleton (closedHomEquiv A D _ _ s) (0 : Fin 1)

/-- 元の閉 pinched 頂点の定数族の各単体は、同じ標準閉定数単体。 -/
lemma pinchedClosedStandardSimplex_const_app {K : SSet.{max u v}} {x y : D}
    (s : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    {n : ℕ} (k : K _⦋n⦌) :
    (SSet.const (X := K) (pinchedClosedVertex A D s)).app _ k =
      pinchedClosedStandardSimplex A D s n := by
  let α := (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
  let e : SSet.uliftFunctor.{v, u}.obj (standardHomSpace (R := A) x y) ≅
      DGNerve.pinchedHom A D x y := standardHomPinchedIso x y
  let v₀ : (SSet.uliftFunctor.{v, u}.obj (standardHomSpace (R := A) x y)) _⦋0⦌ :=
    ULift.up (standardConstant (closedHomEquiv A D _ _ s) 0)
  have ht := ConcreteCategory.congr_hom (e.hom.naturality α) v₀
  change (standardHomPinchedIso (R := A) (D := D) x y).hom.app (Opposite.op ⦋n⦌) (ULift.up
      (standardPullback (OrderHom.const (Fin (n + 1)) (0 : Fin 1))
        (standardConstant (closedHomEquiv A D _ _ s) 0))) =
    (DGNerve.pinchedHom A D x y).map α (pinchedClosedStandardSimplex A D s 0) at ht
  rw [standardConstant_pullback, pinchedClosedStandardSimplex_zero] at ht
  exact ht.symm

/-- 全パラメータ族と指定実閉辺の定数族の AW 合成は、同じ実閉辺の後合成。 -/
lemma pinchedHomCompositionFamily_closed_post {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ DGNerve.pinchedHom A D x y)
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z) :
    pinchedHomCompositionFamily f (SSet.const (pinchedClosedVertex A D s)) =
      f ≫ pinchedClosedPostcomposition A D s := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  change (pinchedHomComposition x y z).app _
      (f.app _ k, (SSet.const (X := K) (pinchedClosedVertex A D s)).app _ k) = _
  rw [pinchedClosedStandardSimplex_const_app, pinchedHomComposition_closed_post]
  rfl

/-- 指定実閉辺の定数族と全パラメータ族の AW 合成は、同じ実閉辺の前合成。 -/
lemma pinchedHomCompositionFamily_closed_pre [Small.{u} D]
    {K : SSet.{max u v}} {x y z : D}
    (s : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y)
    (g : K ⟶ DGNerve.pinchedHom A D y z) :
    pinchedHomCompositionFamily (SSet.const (pinchedClosedVertex A D s)) g =
      g ≫ pinchedClosedPrecomposition A D s := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  change (pinchedHomComposition x y z).app _
      ((SSet.const (X := K) (pinchedClosedVertex A D s)).app _ k, g.app _ k) = _
  rw [pinchedClosedStandardSimplex_const_app, pinchedHomComposition_closed_pre]
  rfl

end SerrePositivity.InfinityCategories
