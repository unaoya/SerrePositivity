module
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedVertexSlice
public import SerrePositivity.InfinityCategories.Derived.PinchedLinearBoundaryEdge
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedPrecomposition

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 閉 pinched 頂点の線形零成分は、元の閉射の cycle。 -/
lemma pinchedClosedVertex_linearValue {q y : D}
    (f : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) y) :
    pinchedLinearVertexValue (toLinearSimplex (pinchedClosedVertex A D f)) =
      (closedHomEquiv A D _ _ f).val := by
  have hI : withLast (Finset.univ : Finset (Fin 1)) = Finset.univ := by decide
  have ha : (Finset.univ.min' (Finset.univ_nonempty :
      (Finset.univ : Finset (Fin 1)).Nonempty)).castSucc = (0 : Fin 2) := by decide
  refine eq_of_heq ((toLinearData_component_heq (pinchedClosedVertex A D f)
    Finset.univ 0 Finset.univ_nonempty (by decide)).trans ?_)
  refine ((pinchedClosedVertex A D f).val.toSimplexData.hom_heq_of_indices_degree
    (hJ := by decide) (hc := by decide) (hd := by decide) (hl := by decide)
    hI ha (show Fin.last 1 = (1 : Fin 2) from rfl) rfl).trans ?_
  rfl

/-- dg 関手の Hom 鎖写像は、閉 pinched 頂点を元の閉射の像の頂点へ送る。 -/
lemma pinchedClosedVertex_map {E : Type v} [DGCategory A E] (F : DGFunctor A D E)
    {q y : D}
    (f : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) y) :
    (pinchedHomChainMap (F.map q y)).app (Opposite.op ⦋0⦌) (pinchedClosedVertex A D f) =
      pinchedClosedVertex A E (F.onClosed.map f) := by
  rw [← dgFunctor_pinchedHomMap_eq]
  apply PinchedHom.Simplex.ext
  exact (pinchedEndpointIso_hom_val _ _ _).trans (dgClosedEdge_map A D F f)

/-- 零次元の線形単体は、唯一の全成分で決まる。 -/
lemma pinchedLinearVertexValue_injective {q y : D} :
    Function.Injective (pinchedLinearVertexValue (A := A) (x := q) (y := y)) := by
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
lemma pinchedClosedVertex_eta {q y : D} (s : (DGNerve.pinchedHom A D q y) _⦋0⦌) :
    pinchedClosedVertex A D (vertexClosedEquiv q y s) = s :=
  (vertexClosedEquiv q y).symm_apply_apply s

/-- 線形単体の鎖写像像と、実 pinched 写像で写した単体は全次元で一致する。 -/
lemma pinchedHomChainMap_toPinched {E : Type v} [DGCategory A E] {q y : D} {q' y' : E}
    (φ : homObject A D q y ⟶ homObject A E q' y') {n : ℕ}
    (s : LinearSimplex A q y n) :
    (pinchedHomChainMap φ).app (Opposite.op ⦋n⦌) s.toPinched =
      (pinchedLinearSimplexMap φ s).toPinched := by
  change (pinchedLinearSimplexMap φ (toLinearSimplex s.toPinched)).toPinched = _
  rw [LinearSimplex.toLinearSimplex_toPinched]

variable [Small.{u} D]

/-- 閉前合成鎖写像は、閉 pinched 頂点の元の閉射の前合成と一致する。 -/
lemma pinchedClosedVertex_precompose {p q y : D}
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (f : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) y) :
    (pinchedClosedPrecomposition A D (y := y) r).app (Opposite.op ⦋0⦌)
      (pinchedClosedVertex A D f) = pinchedClosedVertex A D (r ≫ f) := by
  apply (linearEquiv p y 0).injective
  apply pinchedLinearVertexValue_injective A D
  change pinchedLinearVertexValue (toLinearSimplex
    (pinchedHomChainMapSimplex (dgClosedPrecomposition A D r) (pinchedClosedVertex A D f))) = _
  rw [pinchedHomChainMapSimplex_linear]
  change (dgClosedPrecomposition A D r).f 0
    (pinchedLinearVertexValue (toLinearSimplex (pinchedClosedVertex A D f))) =
      pinchedLinearVertexValue (toLinearSimplex (pinchedClosedVertex A D (r ≫ f)))
  rw [pinchedClosedVertex_linearValue, pinchedClosedVertex_linearValue, dgClosedPrecomposition_f]
  exact (HomotopyComparison.closedHom_comp r f).symm

end SerrePositivity.InfinityCategories
