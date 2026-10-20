module
public import SerrePositivity.InfinityCategories.Derived.DGClosedPostcompositionLaws
public import SerrePositivity.InfinityCategories.Derived.DGFiniteHomotopyDescent
public import SerrePositivity.InfinityCategories.Derived.DGQuotientRoofRefinementEquivalence
public import SerrePositivity.InfinityCategories.Derived.WeakHomotopyDescent

/-! # 有限パラメータの実閉分母による Ore 細分

概要：有限族の分子を、指定された右側分母へ一斉に持ち上げる実細分を構成する。
方針：商で後合成を逆にし、係数を実現した後、指定両端の商ホモトピーを下降する。
規約：二段の実閉分母と元の Hom 内の全ホモトピーを保持する。
使われ方：実屋根の合成を有限図式に拡張する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) {K : SSet.{max u v}} {x y z : D}
variable (f : K ⟶ DGNerve.pinchedHom A D x y)
variable (s : ForgetEnrichment.of (Complex A) z ⟶ ForgetEnrichment.of (Complex A) y)

/-- 有限族の分子と指定右分母を結ぶ二段の実 Ore 細分。 -/
structure DGFiniteOreRefinement where
  source : D
  denominator : ForgetEnrichment.of (Complex A) source ⟶ ForgetEnrichment.of (Complex A) x
  denominator_mem : (dgClosedEdge A D denominator).edge ∈ dgVerdierEdges A D P
  refinedSource : D
  refinement : ForgetEnrichment.of (Complex A) refinedSource ⟶
    ForgetEnrichment.of (Complex A) source
  refinement_mem : (dgClosedEdge A D refinement).edge ∈ dgVerdierEdges A D P
  lift : K ⟶ DGNerve.pinchedHom A D refinedSource z
  homotopy : SSet.Homotopy
    (f ≫ pinchedClosedPrecomposition A D denominator ≫
      pinchedClosedPrecomposition A D refinement)
    (lift ≫ pinchedClosedPostcomposition A D s)

/-- 二段細分の合成実閉分母。 -/
def DGFiniteOreRefinement.combinedDenominator (R : DGFiniteOreRefinement A D P f s) :
    ForgetEnrichment.of (Complex A) R.refinedSource ⟶ ForgetEnrichment.of (Complex A) x :=
  R.refinement ≫ R.denominator

/-- 合成した分母も同じ実 Verdier 辺集合に属する。 -/
lemma DGFiniteOreRefinement.combinedDenominator_mem [IsDGPretriangulated A D]
    (R : DGFiniteOreRefinement A D P f s) :
    (dgClosedEdge A D R.combinedDenominator).edge ∈ dgVerdierEdges A D P :=
  dgClosedVerdierDenominator_comp A D P R.refinement R.denominator
    R.refinement_mem R.denominator_mem

/-- 合成実閉分母による前合成と指定右分母による後合成を結ぶ全ホモトピー。 -/
def DGFiniteOreRefinement.combinedHomotopy (R : DGFiniteOreRefinement A D P f s) :
    SSet.Homotopy (f ≫ pinchedClosedPrecomposition A D R.combinedDenominator)
      (R.lift ≫ pinchedClosedPostcomposition A D s) := by
  refine stableHomotopyRetarget R.homotopy ?_ rfl
  dsimp only [DGFiniteOreRefinement.combinedDenominator, pinchedClosedPrecomposition]
  rw [← pinchedHomChainMap_comp, dgClosedPrecomposition_comp]

/-- 任意の有限族と指定閉分母は、元の Hom 内のホモトピーを伴う実 Ore 細分を持つ。 -/
theorem dgFiniteOreRefinement_nonempty [IsDGPretriangulated A D] [K.Finite]
    (hP : localKFlat A D P)
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P) :
    Nonempty (DGFiniteOreRefinement A D P f s) := by
  let Q := inclusion A D P
  let sq := Q.onClosed.map s
  let post := pinchedClosedPostcomposition A (QuotientObject D P)
    (x := Q.obj x) sq
  obtain ⟨j, _, ⟨Hj⟩⟩ :=
    pinchedClosedPostcomposition_equivalence_of_invertible A (QuotientObject D P)
      (x := Q.obj x) sq (dgQuotientClosedDenominator_isInvertible A D P hP s hs)
  let g := f ≫ pinchedHomChainMap (Q.map x y) ≫ j
  let a : ((⊥ : K.Subcomplex) : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x z :=
    Subcomplex.isInitialBot.to _
  obtain ⟨R⟩ := dgCoefficientFinitePairs_nonempty A D P (⊥ : K.Subcomplex).ι x z a g hP
    (Subcomplex.isInitialBot.hom_ext _ _)
  let p := pinchedClosedPrecomposition A D (y := y) R.denominator
  let b := R.filler ≫ pinchedClosedPostcomposition A D s
  have Hleft : Nonempty (SSet.Homotopy
      (g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
        (q := Q.obj R.source) (x := Q.obj x) (y := Q.obj z)
        (Q.onClosed.map R.denominator) ≫
        pinchedClosedPostcomposition A (QuotientObject D P) (x := Q.obj R.source) sq)
      (f ≫ p ≫ pinchedHomChainMap (Q.map R.source y))) := by
    let H := functorHomotopyPostcomp
      (functorHomotopyPrecomp Hj (f ≫ pinchedHomChainMap (Q.map x y)))
      (pinchedClosedPrecomposition A (QuotientObject D P)
        (q := Q.obj R.source) (x := Q.obj x) (y := Q.obj y)
        (Q.onClosed.map R.denominator))
    refine ⟨stableHomotopyRetarget H ?_ ?_⟩
    · dsimp only [g]
      simp only [Category.assoc, pinchedClosedPostcomposition_precomposition]
    · dsimp only [p]
      simp only [Category.id_comp, Category.assoc]
      have hn := dgClosedPrecomposition_naturality A D (QuotientObject D P) Q
        (y := y) R.denominator
      have hp := congrArg (fun k => f ≫ pinchedHomChainMap k) hn.symm
      simpa only [pinchedHomChainMap_comp, Category.assoc,
        pinchedClosedPrecomposition] using! hp
  have Hright : Nonempty (SSet.Homotopy
      (g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
        (q := Q.obj R.source) (x := Q.obj x) (y := Q.obj z)
        (Q.onClosed.map R.denominator) ≫
        pinchedClosedPostcomposition A (QuotientObject D P) (x := Q.obj R.source) sq)
      (b ≫ pinchedHomChainMap (Q.map R.source y))) := by
    let H := functorHomotopyPostcomp R.comparison
      (pinchedClosedPostcomposition A (QuotientObject D P) (x := Q.obj R.source) sq)
    refine ⟨stableHomotopyRetarget H (Category.assoc _ _ _) ?_⟩
    dsimp only [b]
    have hn := pinchedClosedPostcomposition_naturality A D (QuotientObject D P) Q
      (x := R.source) s
    have hp := congrArg (fun k => R.filler ≫ k) hn.symm
    simpa only [Category.assoc] using! hp
  obtain ⟨H⟩ : Nonempty (SSet.Homotopy
      ((f ≫ p) ≫ pinchedHomChainMap (Q.map R.source y))
      (b ≫ pinchedHomChainMap (Q.map R.source y))) := by
    apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
    exact ((functorVertex_piZero_eq_iff_homotopy _ _).mpr Hleft).symm.trans
      ((functorVertex_piZero_eq_iff_homotopy _ _).mpr Hright)
  obtain ⟨T⟩ := dgFiniteHomotopyDescent_nonempty A D P R.source y (f ≫ p) b H hP
  refine ⟨⟨R.source, R.denominator, R.denominator_mem, T.source, T.denominator,
    T.denominator_mem, R.filler ≫ pinchedClosedPrecomposition A D T.denominator,
    stableHomotopyRetarget T.homotopy ?_ ?_⟩⟩
  · exact Category.assoc _ _ _
  · dsimp only [b]
    rw [Category.assoc, pinchedClosedPostcomposition_precomposition, ← Category.assoc]

end SerrePositivity.InfinityCategories
