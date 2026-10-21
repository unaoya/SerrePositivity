module
public import SerrePositivity.InfinityCategories.DGNerve.Quasicategory
public import SerrePositivity.InfinityCategories.F1B.IntervalComposition
public import SerrePositivity.InfinityCategories.Derived.DGPinchedFamilyComposition
public import SerrePositivity.InfinityCategories.Derived.ConstantEdgeFamily
public import SerrePositivity.InfinityCategories.Derived.DGClosedPostcompositionEquivalence
/-!
概要：元の閉 dg 射による後合成を、標準区間模型の同じ後合成へ照合する。
方針：同じ実ホモトピーを反転し、任意パラメータ族の合成表示で比較する。
規約：標準の写像空間比較と元の全関手を保持する。使われ方：一般 RHom の ∞ 随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open DifferentialGraded DGNerve
open scoped Simplicial

/-- 元の閉 dg 射の pinched 後合成は、標準区間模型の同じ射の後合成とホモトピック。 -/
lemma dgClosedPostcomposition_interval_homotopy (R : Type u) [CommRing R]
    (C : Type v) [DGCategory R C] (x y z : C)
    (f : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z) :
    Nonempty (SSet.Homotopy
      (pinchedClosedPostcomposition R C (x := x) f ≫
        pinchedHomToIntervalMappingSpace (X := dgNerve R C) (Simplex.vertex x) (Simplex.vertex z))
      (pinchedHomToIntervalMappingSpace (X := dgNerve R C) (Simplex.vertex x) (Simplex.vertex y) ≫
        intervalPostcompose (X := dgNerve R C) (Simplex.vertex x)
        (y := Simplex.vertex y) (y' := Simplex.vertex z)
        (Truncated.HomotopyCategory.homMk (dgClosedEdge R C f)))) := by
  let L : DGNerve.pinchedHom R C x y ⟶
      intervalMappingSpace (X := dgNerve R C) (Simplex.vertex x) (Simplex.vertex z) :=
    pinchedClosedPostcomposition R C (x := x) f ≫
      pinchedHomToIntervalMappingSpace (X := dgNerve R C) (Simplex.vertex x) (Simplex.vertex z)
  let U : DGNerve.pinchedHom R C x y ⟶
      intervalMappingSpace (X := dgNerve R C) (Simplex.vertex x) (Simplex.vertex z) :=
    pinchedHomToIntervalMappingSpace (X := dgNerve R C) (Simplex.vertex x) (Simplex.vertex y) ≫
      intervalPostcompose (X := dgNerve R C) (Simplex.vertex x)
        (y := Simplex.vertex y) (y' := Simplex.vertex z)
        (Truncated.HomotopyCategory.homMk (dgClosedEdge R C f))
  refine intervalFamilyHom_eq_imp_homotopy
    (A := DGNerve.pinchedHom R C x y) (X := dgNerve R C)
    (x := Simplex.vertex x) (y := Simplex.vertex z) (f := L) (g := U) ?_
  change intervalFamilyHom (_ ≫ _) = intervalFamilyHom (_ ≫ _)
  rw [intervalPostcompose_family]
  have hc := dgPinchedFamilyHom_comp R C (𝟙 (DGNerve.pinchedHom R C x y))
    (SSet.const (pinchedClosedVertex R C f))
  rw [pinchedHomCompositionFamily_closed_post, Category.id_comp] at hc
  have hconst : dgPinchedFamilyHom R C
      (SSet.const (X := DGNerve.pinchedHom R C x y) (pinchedClosedVertex R C f)) =
      constantFunctorHomMap (DGNerve.pinchedHom R C x y)
        (Truncated.HomotopyCategory.homMk (dgClosedEdge R C f)) :=
    pinchedFamilyHom_const_vertex (K := DGNerve.pinchedHom R C x y)
      (X := dgNerve R C) (pinchedClosedVertex R C f)
  rw [hconst] at hc
  simpa only [dgPinchedFamilyHom, Category.id_comp] using hc.symm
end SerrePositivity.InfinityCategories
