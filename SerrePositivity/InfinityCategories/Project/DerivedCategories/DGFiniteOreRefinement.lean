module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPostcompositionLaws
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteHomotopyDescent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientRoofRefinementEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.WeakHomotopyDescent

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) {K : SSet.{max u v}} {x y z : D}
variable (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)

/-- 有限族の分子と指定右分母を結ぶ二段の実 Ore 細分。 -/
structure DGFiniteOreRefinement where
  source : D
  denominator : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) source ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x
  denominator_mem : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D denominator).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P
  refinedSource : D
  refinement : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) refinedSource ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) source
  refinement_mem : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D refinement).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P
  lift : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D refinedSource z
  homotopy : SSet.Homotopy
    (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D denominator ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D refinement)
    (lift ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition A D s)

/-- 二段細分の合成実閉分母。 -/
def DGFiniteOreRefinement.combinedDenominator (R : DGFiniteOreRefinement A D P f s) :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) R.refinedSource ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x :=
  R.refinement ≫ R.denominator

/-- 合成した分母も同じ実 Verdier 辺集合に属する。 -/
lemma DGFiniteOreRefinement.combinedDenominator_mem [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (R : DGFiniteOreRefinement A D P f s) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D R.combinedDenominator).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_comp A D P R.refinement R.denominator
    R.refinement_mem R.denominator_mem

/-- 合成実閉分母による前合成と指定右分母による後合成を結ぶ全ホモトピー。 -/
def DGFiniteOreRefinement.combinedHomotopy (R : DGFiniteOreRefinement A D P f s) :
    SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D R.combinedDenominator)
      (R.lift ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition A D s) := by
  refine _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget R.homotopy ?_ rfl
  dsimp only [DGFiniteOreRefinement.combinedDenominator, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_comp]

/-- 任意の有限族と指定閉分母は、元の Hom 内のホモトピーを伴う実 Ore 細分を持つ。 -/
theorem dgFiniteOreRefinement_nonempty [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] [K.Finite]
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    Nonempty (DGFiniteOreRefinement A D P f s) := by
  let Q := _root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P
  let sq := Q.onClosed.map s
  let post := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition A (QuotientObject D P)
    (x := Q.obj x) sq
  obtain ⟨j, _, ⟨Hj⟩⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition_equivalence_of_invertible A (QuotientObject D P)
      (x := Q.obj x) sq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedDenominator_isInvertible A D P hP s hs)
  let g := f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map x y) ≫ j
  let a : ((⊥ : K.Subcomplex) : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x z :=
    Subcomplex.isInitialBot.to _
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoefficientFinitePairs_nonempty A D P (⊥ : K.Subcomplex).ι x z a g hP
    (Subcomplex.isInitialBot.hom_ext _ _)
  let p := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := y) R.denominator
  let b := R.filler ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition A D s
  have Hleft : Nonempty (SSet.Homotopy
      (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
        (q := Q.obj R.source) (x := Q.obj x) (y := Q.obj z)
        (Q.onClosed.map R.denominator) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition A (QuotientObject D P) (x := Q.obj R.source) sq)
      (f ≫ p ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map R.source y))) := by
    let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp Hj (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map x y)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
        (q := Q.obj R.source) (x := Q.obj x) (y := Q.obj y)
        (Q.onClosed.map R.denominator))
    refine ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget H ?_ ?_⟩
    · dsimp only [g]
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition_precomposition]
    · dsimp only [p]
      simp only [Category.id_comp, Category.assoc]
      have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_naturality A D (QuotientObject D P) Q
        (y := y) R.denominator
      have hp := congrArg (fun k => f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap k) hn.symm
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition] using! hp
  have Hright : Nonempty (SSet.Homotopy
      (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
        (q := Q.obj R.source) (x := Q.obj x) (y := Q.obj z)
        (Q.onClosed.map R.denominator) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition A (QuotientObject D P) (x := Q.obj R.source) sq)
      (b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map R.source y))) := by
    let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp R.comparison
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition A (QuotientObject D P) (x := Q.obj R.source) sq)
    refine ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget H (Category.assoc _ _ _) ?_⟩
    dsimp only [b]
    have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition_naturality A D (QuotientObject D P) Q
      (x := R.source) s
    have hp := congrArg (fun k => R.filler ≫ k) hn.symm
    simpa only [Category.assoc] using! hp
  obtain ⟨H⟩ : Nonempty (SSet.Homotopy
      ((f ≫ p) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map R.source y))
      (b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map R.source y))) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr Hleft).symm.trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr Hright)
  obtain ⟨T⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteHomotopyDescent_nonempty A D P R.source y (f ≫ p) b H hP
  refine ⟨⟨R.source, R.denominator, R.denominator_mem, T.source, T.denominator,
    T.denominator_mem, R.filler ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D T.denominator,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget T.homotopy ?_ ?_⟩⟩
  · exact Category.assoc _ _ _
  · dsimp only [b]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition_precomposition, ← Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
