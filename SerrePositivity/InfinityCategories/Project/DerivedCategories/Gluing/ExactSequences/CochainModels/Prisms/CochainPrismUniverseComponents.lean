module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.CochainPinchedInputComponents

/-! 異なる対象宇宙の cochain prism は、同じ入力係数・二端・primitive の写像で比較できる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex DifferentialGraded CochainComplex HomComplex

open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) (T : Type (max u w))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R T] (x y : E) (x' y' : T) (K : _root_.SerrePositivity.DifferentialGraded.Complex R)
  (f g : K ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E x y) (h : Cochain K (_root_.SerrePositivity.DifferentialGraded.homObject R E x y) (-1))
  (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  (f' g' : K ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R T x' y') (h' : Cochain K (_root_.SerrePositivity.DifferentialGraded.homObject R T x' y') (-1))
  (he' : δ (-1) 0 h' = Cochain.ofHom (g' - f'))
  (q : _root_.SerrePositivity.DifferentialGraded.homObject R E x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R T x' y')
  (hf : f ≫ q = f') (hg : g ≫ q = g')
  (hh : h.comp (Cochain.ofHom q) (add_zero (-1)) = h')
  {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v} K) _⦋n⦌)
  (t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u w} K) _⦋n⦌)
  (hs : ∀ J p hJ hp, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J p hJ hp =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData t).component J p hJ hp)

include hf hg hh hs in
lemma dgGluingCochainPrism_universe_component
    (β : Fin (n + 1) →o Fin 2) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    q.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrismSimplex R E
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput.{u, v} R E x y K f g h he).app
        (Opposite.op ⦋n⦌) s) β)).component J k hJ hk) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrismSimplex R T
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput.{u, w} R T x' y' K f' g' h' he').app
          (Opposite.op ⦋n⦌) t) β)).component J k hJ hk := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_component_post_compare
  · intro J p hJ hp
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPinchedInput_source, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPinchedInput_source, ← hs J p hJ hp]
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hg p) _
  · intro J p hJ hp
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPinchedInput_replacement, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPinchedInput_replacement,
      ← hs J p hJ hp]
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hf p) _
  · intro J p hJ hp
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPinchedInput_primitive, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPinchedInput_primitive,
      ← hs J p hJ hp]
    have hn : (-h).comp (Cochain.ofHom q) (add_zero (-1)) = -h' := by
      rw [Cochain.neg_comp, hh]
    have hd := ConcreteCategory.congr_hom (Cochain.congr_v hn p (p - 1) (by omega))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv.f p ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J p hJ hp))
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ModuleCat.comp_apply] using hd

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
