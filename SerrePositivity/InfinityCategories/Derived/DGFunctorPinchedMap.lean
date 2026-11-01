module
public import SerrePositivity.InfinityCategories.Derived.PinchedHomChainMap
public import SerrePositivity.InfinityCategories.Core.Roof.PinchedEndpointTransport
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects

/-! # dg 関手による pinched 写像空間の射と Hom 鎖写像の照合

概要：実際の nerve の射の作用を線形表示の鎖写像と同定する。
方針：端点の等式を明示的に輸送し、全成分を異種等号で照合する。
規約：端点の輸送同型を省略しない。使われ方：β3 の充満忠実性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

/-- dg 関手による斉次射の像は対象と成分の異種等号を保存。 -/
lemma dgFunctor_map_component_heq (F : DGFunctor A D E) {a b x y : D}
    (ha : a = x) (hb : b = y) (k : ℤ) {f : GradedHom A a b k} {g : GradedHom A x y k}
    (h : HEq f g) : HEq ((F.map a b).f k f) ((F.map x y).f k g) := by
  subst x
  subst y
  cases h
  rfl

/-- 端点を標準頂点へ輸送した実際の nerve の写像空間の射は Hom 鎖写像の射に等しい。 -/
lemma dgFunctor_pinchedHomMap_eq (F : DGFunctor A D E) (x y : D) :
    pinchedHomMap (dgNerve.map F) (Simplex.vertex x) (Simplex.vertex y) ≫
      (pinchedEndpointIso (dgFunctorNerve_vertex F x) (dgFunctorNerve_vertex F y)).hom =
        pinchedHomChainMap (F.map x y) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply (linearEquiv (F.obj x) (F.obj y) n.unop.len).injective
  change toLinearSimplex ((pinchedEndpointIso (dgFunctorNerve_vertex F x)
    (dgFunctorNerve_vertex F y)).hom.app n
      (pinchedSimplexMap (dgNerve.map F) s)) =
    toLinearSimplex (pinchedHomChainMapSimplex (F.map x y) s)
  rw [pinchedHomChainMapSimplex_linear]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  let t := (pinchedEndpointIso (dgFunctorNerve_vertex F x)
    (dgFunctorNerve_vertex F y)).hom.app n (pinchedSimplexMap (dgNerve.map F) s)
  change (toLinearData t).component J k hJ hk =
    (F.map x y).f k ((toLinearData s).component J k hJ hk)
  apply eq_of_heq
  have ht := toLinearData_component_heq t J k hJ hk
  have hv : t.val = s.val.map F := pinchedEndpointIso_hom_val _ _ _
  rw [hv] at ht
  exact ht.trans (dgFunctor_map_component_heq F (source_obj s (J.min' hJ))
    (target_obj s) k (toLinearData_component_heq s J k hJ hk).symm)

end SerrePositivity.InfinityCategories
