module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedHomClosedComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedClosedVertexNaturality

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
/-- 標準 DK 座標で作った閉定数の頂点は、元の指定閉辺の pinched 頂点。 -/
lemma pinchedClosedStandardSimplex_zero {x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedStandardSimplex A D s 0 = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomStandard_injective x y 0
  dsimp only
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedStandardSimplex_coordinates, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomStandard_coordinates]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv x y).injective
  apply Subtype.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A D _ _ s) 0).val.component
    Finset.univ 0 Finset.univ_nonempty (by decide) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s)).val).component
        Finset.univ 0 Finset.univ_nonempty (by decide)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData_component]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A D _ _ s) 0).val.component
    Finset.univ 0 Finset.univ_nonempty (by decide) =
      (1 : ℤ) • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s))
  rw [one_smul, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedVertexNaturality.pinchedClosedVertex_linearValue]
  simpa only [show (Finset.univ : Finset (Fin 1)) = {0} from by decide] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant_singleton (closedHomEquiv A D _ _ s) (0 : Fin 1)

/-- 元の閉 pinched 頂点の定数族の各単体は、同じ標準閉定数単体。 -/
lemma pinchedClosedStandardSimplex_const_app {K : SSet.{max u v}} {x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
    {n : ℕ} (k : K _⦋n⦌) :
    (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s)).app _ k =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedStandardSimplex A D s n := by
  let α := (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
  let e : SSet.uliftFunctor.{v, u}.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := A) x y) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x y
  let v₀ : (SSet.uliftFunctor.{v, u}.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := A) x y)) _⦋0⦌ :=
    ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s) 0)
  have ht := ConcreteCategory.congr_hom (e.hom.naturality α) v₀
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x y).hom.app (Opposite.op ⦋n⦌) (ULift.up
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback (OrderHom.const (Fin (n + 1)) (0 : Fin 1))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A D _ _ s) 0))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y).map α (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedStandardSimplex A D s 0) at ht
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant_pullback, pinchedClosedStandardSimplex_zero] at ht
  exact ht.symm

/-- 全パラメータ族と指定実閉辺の定数族の AW 合成は、同じ実閉辺の後合成。 -/
lemma pinchedHomCompositionFamily_closed_post {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily f (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s)) =
      f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition A D s := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition x y z).app _
      (f.app _ k, (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s)).app _ k) = _
  rw [pinchedClosedStandardSimplex_const_app, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomComposition_closed_post]
  rfl

/-- 指定実閉辺の定数族と全パラメータ族の AW 合成は、同じ実閉辺の前合成。 -/
lemma pinchedHomCompositionFamily_closed_pre [Small.{u} D]
    {K : SSet.{max u v}} {x y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s)) g =
      g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D s := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition x y z).app _
      ((SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D s)).app _ k, g.app _ k) = _
  rw [pinchedClosedStandardSimplex_const_app, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomComposition_closed_pre]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
