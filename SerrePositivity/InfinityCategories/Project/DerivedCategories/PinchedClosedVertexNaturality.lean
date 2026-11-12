module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedVertexSlice
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedLinearBoundaryEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedPrecomposition

/-! # 閉 pinched 頂点の関手性と前合成

概要：閉射の pinched 頂点を dg 関手と元の閉前合成に沿って計算する。
方針：元の辺と線形零次元成分を比較する。
規約：閉射の恒等式を保つ。使われ方：有限頂点持ち上げの実屋根端点の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedVertexNaturality
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 閉 pinched 頂点の線形零成分は、元の閉射の cycle。 -/
lemma pinchedClosedVertex_linearValue {q y : D}
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D f)) =
      (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ f).val := by
  have hI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast (Finset.univ : Finset (Fin 1)) = Finset.univ := by decide
  have ha : (Finset.univ.min' (Finset.univ_nonempty :
      (Finset.univ : Finset (Fin 1)).Nonempty)).castSucc = (0 : Fin 2) := by decide
  refine eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_component_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D f)
    Finset.univ 0 Finset.univ_nonempty (by decide)).trans ?_)
  refine ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D f).val.toSimplexData.hom_heq_of_indices_degree
    (hJ := by decide) (hc := by decide) (hd := by decide) (hl := by decide)
    hI ha (show Fin.last 1 = (1 : Fin 2) from rfl) rfl).trans ?_
  rfl

/-- dg 関手の Hom 鎖写像は、閉 pinched 頂点を元の閉射の像の頂点へ送る。 -/
lemma pinchedClosedVertex_map {E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    {q y : D}
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map q y)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D f) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A E (F.onClosed.map f) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_pinchedHomMap_eq]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso_hom_val _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map A D F f)

/-- 零次元の線形単体は、唯一の全成分で決まる。 -/
lemma pinchedLinearVertexValue_injective {q y : D} :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue (A := A) (x := q) (y := y)) := by
  intro s t h
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  have hfull : J = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro j
    obtain ⟨a, ha⟩ := hJ
    have haj : a = j := by omega
    simpa only [haj] using ha
  subst J
  have hk0 : k = 0 := by simpa using hk
  subst k
  exact h

/-- 任意の pinched 頂点は、その元の閉零射から厳密に復元される。 -/
lemma pinchedClosedVertex_eta {q y : D} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexClosedEquiv q y s) = s :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexClosedEquiv q y).symm_apply_apply s

/-- 線形単体の鎖写像像と、実 pinched 写像で写した単体は全次元で一致する。 -/
lemma pinchedHomChainMap_toPinched {E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] {q y : D} {q' y' : E}
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D q y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E q' y') {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A q y n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ).app (Opposite.op ⦋n⦌) s.toPinched =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap φ s).toPinched := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap φ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s.toPinched)).toPinched = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched]

variable [Small.{u} D]

/-- 閉前合成鎖写像は、閉 pinched 頂点の元の閉射の前合成と一致する。 -/
lemma pinchedClosedVertex_precompose {p q y : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := y) r).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D f) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D (r ≫ f) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv p y 0).injective
  apply pinchedLinearVertexValue_injective A D
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D f))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r).f 0
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D f))) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearVertexValue (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D (r ≫ f)))
  rw [pinchedClosedVertex_linearValue, pinchedClosedVertex_linearValue, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_f]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp r f).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedVertexNaturality
