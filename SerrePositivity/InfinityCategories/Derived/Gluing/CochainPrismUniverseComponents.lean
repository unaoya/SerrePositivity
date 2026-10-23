module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainPinchedInputComponents

/-! 異なる対象宇宙の cochain prism は、同じ入力係数・二端・primitive の写像で比較できる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex DifferentialGraded CochainComplex HomComplex
open DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) (T : Type (max u w))
  [DGCategory R E] [DGCategory R T] (x y : E) (x' y' : T) (K : Complex R)
  (f g : K ⟶ homObject R E x y) (h : Cochain K (homObject R E x y) (-1))
  (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  (f' g' : K ⟶ homObject R T x' y') (h' : Cochain K (homObject R T x' y') (-1))
  (he' : δ (-1) 0 h' = Cochain.ofHom (g' - f'))
  (q : homObject R E x y ⟶ homObject R T x' y')
  (hf : f ≫ q = f') (hg : g ≫ q = g')
  (hh : h.comp (Cochain.ofHom q) (add_zero (-1)) = h')
  {n : ℕ} (s : (complexPinchedSpace.{u, max u v} K) _⦋n⦌)
  (t : (complexPinchedSpace.{u, max u w} K) _⦋n⦌)
  (hs : ∀ J p hJ hp, (toLinearData s).component J p hJ hp =
    (toLinearData t).component J p hJ hp)

include hf hg hh hs in
lemma dgGluingCochainPrism_universe_component
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    q.f k ((toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R E
      ((dgGluingCochainIdentityCommaPinchedInput.{u, v} R E x y K f g h he).app
        (Opposite.op ⦋n⦌) s) β)).component J k hJ hk) =
      (toLinearData (dgGluingIdentityCommaPinchedPrismSimplex R T
        ((dgGluingCochainIdentityCommaPinchedInput.{u, w} R T x' y' K f' g' h' he').app
          (Opposite.op ⦋n⦌) t) β)).component J k hJ hk := by
  apply dgGluingIdentityCommaPrism_component_post_compare
  · intro J p hJ hp
    rw [dgGluingCochainPinchedInput_source, dgGluingCochainPinchedInput_source, ← hs J p hJ hp]
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hg p) _
  · intro J p hJ hp
    rw [dgGluingCochainPinchedInput_replacement, dgGluingCochainPinchedInput_replacement,
      ← hs J p hJ hp]
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hf p) _
  · intro J p hJ hp
    rw [dgGluingCochainPinchedInput_primitive, dgGluingCochainPinchedInput_primitive,
      ← hs J p hJ hp]
    have hn : (-h).comp (Cochain.ofHom q) (add_zero (-1)) = -h' := by
      rw [Cochain.neg_comp, hh]
    have hd := ConcreteCategory.congr_hom (Cochain.congr_v hn p (p - 1) (by omega))
      ((complexUnitHomIso K).inv.f p ((toLinearData s).component J p hJ hp))
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ModuleCat.comp_apply] using hd

end SerrePositivity.InfinityCategories
