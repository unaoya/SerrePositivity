module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseHomChainMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseNerveMap
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap

/-! 元の一般宇宙の dg 関手の全 pinched Hom 作用を、その Hom 鎖写像へ照合する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} {D : Type w}
  [DGCategory R C] [DGCategory R D]

lemma dgGluingFunctor_map_component_heq (F : DGFunctor R C D) {a b x y : C}
    (ha : a = x) (hb : b = y) (k : ℤ) {f : GradedHom R a b k} {g : GradedHom R x y k}
    (h : HEq f g) : HEq ((F.map a b).f k f) ((F.map x y).f k g) := by
  subst x
  subst y
  cases h
  rfl

lemma dgGluingUniverseFunctorHomAction (F : DGFunctor R C D) (x y : C) :
    (uliftPinchedHomIso.{max u v, max w r}
      (C := dgNerve R C) (Simplex.vertex x) (Simplex.vertex y)).hom ≫
      pinchedHomMap (dgGluingUniverseNerveMap.{u, v, w, r} F)
        (ULift.up (Simplex.vertex x)) (ULift.up (Simplex.vertex y)) ≫
      (pinchedEndpointIso (dgGluingUniverseNerveMap_vertex F x)
        (dgGluingUniverseNerveMap_vertex F y)).hom ≫
      (uliftPinchedHomIso.{max u w, max v r}
        (C := dgNerve R D) (Simplex.vertex (F.obj x)) (Simplex.vertex (F.obj y))).inv =
      dgGluingUniverseHomChainMap.{u, v, w, r} (F.map x y) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (linearEquiv (F.obj x) (F.obj y) n.unop.len).injective
  let t := downPinchedSimplex (C := dgNerve R D) (n := n.unop.len)
    ((pinchedEndpointIso (dgGluingUniverseNerveMap_vertex F x)
      (dgGluingUniverseNerveMap_vertex F y)).hom.app n
      (pinchedSimplexMap (dgGluingUniverseNerveMap.{u, v, w, r} F)
        (uliftPinchedSimplex s.down)))
  change toLinearSimplex t = toLinearSimplex
    ((pinchedLinearSimplexMap (F.map x y) (toLinearSimplex s.down)).toPinched)
  rw [LinearSimplex.toLinearSimplex_toPinched]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (toLinearData t).component J k hJ hk =
    (F.map x y).f k ((toLinearData s.down).component J k hJ hk)
  apply eq_of_heq
  have ht := toLinearData_component_heq t J k hJ hk
  have hv : t.val = s.down.val.map F := by
    exact congrArg ULift.down (pinchedEndpointIso_hom_val
      (dgGluingUniverseNerveMap_vertex.{u, v, w, r} F x)
      (dgGluingUniverseNerveMap_vertex.{u, v, w, r} F y)
      (pinchedSimplexMap (dgGluingUniverseNerveMap.{u, v, w, r} F)
        (uliftPinchedSimplex s.down)))
  rw [hv] at ht
  exact ht.trans (dgGluingFunctor_map_component_heq F
    (source_obj s.down (J.min' hJ)) (target_obj s.down) k
    (toLinearData_component_heq s.down J k hJ hk).symm)

end SerrePositivity.InfinityCategories
