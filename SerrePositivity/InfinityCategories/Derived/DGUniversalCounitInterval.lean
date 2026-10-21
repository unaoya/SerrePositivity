module
public import SerrePositivity.InfinityCategories.Derived.IntervalEndpointTransport
public import SerrePositivity.InfinityCategories.Derived.DGClosedPostcompositionInterval
public import SerrePositivity.InfinityCategories.Derived.DGUniversalCounitNative
public import SerrePositivity.InfinityCategories.F1B.PinchedIntervalEquivalence
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
/-!
概要：同じ実普遍余単位の全 pinched Hom 同値を標準区間比較の同値へ移す。
方針：同じ実辺の回収と標準比較の反転を、全パラメータの随伴判定へ渡す。
規約：元の全関手と厳密切断を保持する。使われ方：一般 kernel の実 RHom 随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial

/-- 元の普遍余単位の全写像空間比較は、区間模型の同じ標準比較でも同値。 -/
lemma DGUniversalCounit.nativeIntervalMap_isSimplicialHomotopyEquivalence
    {R : Type u} [CommRing R] {C E : Type v} [DGCategory R C] [DGCategory R E]
    {F : DGFunctor R C E} {y : E} (e : DGUniversalCounit R C E F y) (x : C) :
    IsSimplicialHomotopyEquivalence
      (intervalFunctorMap (dgNerve.map F) (Simplex.vertex x) (Simplex.vertex e.source) ≫
        (intervalEndpointIso (dgFunctorNerve_vertex F x)
          (dgFunctorNerve_vertex F e.source)).hom ≫
        intervalPostcompose (X := dgNerve R E) (Simplex.vertex (F.obj x))
          (y := Simplex.vertex (F.obj e.source)) (y' := Simplex.vertex y)
          (Truncated.HomotopyCategory.homMk (dgClosedEdge R E e.counit))) := by
  let m := pinchedHomMap (dgNerve.map F) (Simplex.vertex x) (Simplex.vertex e.source) ≫
    (pinchedEndpointIso (dgFunctorNerve_vertex F x) (dgFunctorNerve_vertex F e.source)).hom
  obtain ⟨K⟩ := dgClosedPostcomposition_interval_homotopy R E
    (F.obj x) (F.obj e.source) y e.counit
  let K' := functorHomotopyPrecomp K m
  have hm := e.nativePinchedMap_isSimplicialHomotopyEquivalence x
  have hi := (PinchedInterval.comparison_isQCatEquivalence
    (X := dgNerve R E) (Simplex.vertex (F.obj x)) (Simplex.vertex y))
  rw [pinchedInterval_comparison_eq] at hi
  have he := hm.isQCatEquivalence.comp hi
  have ht := he.ofFunctorIso (functorIsoOfSimplicialHomotopy K')
  have hn : m ≫ pinchedHomToIntervalMappingSpace (X := dgNerve R E)
      (Simplex.vertex (F.obj x)) (Simplex.vertex (F.obj e.source)) =
    pinchedHomToIntervalMappingSpace (X := dgNerve R C)
      (Simplex.vertex x) (Simplex.vertex e.source) ≫
        intervalFunctorMap (dgNerve.map F) (Simplex.vertex x) (Simplex.vertex e.source) ≫
          (intervalEndpointIso (dgFunctorNerve_vertex F x)
            (dgFunctorNerve_vertex F e.source)).hom := by
    dsimp only [m]
    rw [Category.assoc, pinchedInterval_endpoint (dgFunctorNerve_vertex F x)
      (dgFunctorNerve_vertex F e.source), ← Category.assoc,
      pinchedHomToIntervalMappingSpace_naturality]
    exact Category.assoc _ _ _
  change IsQCatEquivalence ((m ≫ pinchedHomToIntervalMappingSpace
    (X := dgNerve R E) (Simplex.vertex (F.obj x)) (Simplex.vertex (F.obj e.source))) ≫ _) at ht
  rw [hn] at ht
  simp only [Category.assoc] at ht
  have hs := PinchedInterval.comparison_isQCatEquivalence
    (X := dgNerve R C) (Simplex.vertex x) (Simplex.vertex e.source)
  rw [pinchedInterval_comparison_eq] at hs
  exact (hs.cancel_left ht).isSimplicialHomotopyEquivalence
end SerrePositivity.InfinityCategories
