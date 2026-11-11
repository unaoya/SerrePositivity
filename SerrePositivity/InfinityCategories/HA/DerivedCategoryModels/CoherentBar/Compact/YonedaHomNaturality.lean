module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.RepresentableEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Checks
/-!
概要：代表可能加群の Yoneda 同型を全 Hom 複体で自然な比較へ束ねる。
方針：任意の斉次射と入力要素についての符号相殺式から Hom 鎖写像の等式を得る。
規約：閉次数零射だけの自然性で代用しない。
使われ方：coherent 図式上で Hom を評価関手へ比較する c2 の入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded Opposite CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 代表からの全 Hom と評価との Yoneda 同型は Hom 複体そのものに関して自然。 -/
lemma dgBarCompactYoneda_homNaturality (x : D) (M N : RightModule R D) :
    (leftRepresentable R (representable R x)).map M N ≫
        homPostcompose (moduleHom R D (representable R x) M) (dgYonedaIso R x N).hom =
      (moduleEvaluationDG R D x).map M N ≫
        homPrecompose (dgYonedaIso R x M).hom (N.obj (op x)) := by
  apply hom_naturality_of_apply
  intro q f
  ext p n hn t
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactYoneda_leftAction R D x M N f t hn

/-- 全次数自然性を保持した Yoneda 評価の厳密 dg 自然変換。 -/
def dgBarCompactYoneda_strict (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (leftRepresentable R (representable R x))
      (moduleEvaluationDG R D x) where
  app M := cycleFromUnit _ (closedMap R (dgYonedaIso R x M).hom)
  naturality {M N k} f := by
    change compose (D := Complex R) R
        (cycleFromUnit (homComplex R (moduleHom R D (representable R x) N) (N.obj (op x)))
          (closedMap R (dgYonedaIso R x N).hom)).val
        (((leftRepresentable R (representable R x)).map M N).f k f) (add_zero k) =
      compose (D := Complex R) R ((moduleHomπ R D M N x).f k f)
        (cycleFromUnit (homComplex R (moduleHom R D (representable R x) M) (M.obj (op x)))
          (closedMap R (dgYonedaIso R x M).hom)).val (zero_add k)
    rw [closedMap_cycle, closedMap_cycle, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose]
    have h := congrArg (fun a => a.f k f) (dgBarCompactYoneda_homNaturality R D x M N)
    change (((leftRepresentable R (representable R x)).map M N).f k f).comp
        (Cochain.ofHom (dgYonedaIso R x N).hom) (add_zero k) =
      (Cochain.ofHom (dgYonedaIso R x M).hom).comp
        ((moduleHomπ R D M N x).f k f) (zero_add k) at h
    exact h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
