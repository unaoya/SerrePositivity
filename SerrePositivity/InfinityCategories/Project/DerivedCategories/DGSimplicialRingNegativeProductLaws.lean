module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingNegativeProduct
/-!
概要：実 cochain 負次数乗法の左単位・結合則。
方針：同じ次数同型と実 Moore 乗法則、自然な次数移送を使う。
規約：元の乗法・単位を保持する。使われ方：β5(g) の dg 代数構造。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open scoped TensorProduct
open CategoryTheory MonoidalCategory
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientModuleFunctor
lemma simplicialRingDGCochainDegreeIso_transport
    (A : SimplicialObject RingCat.{u}) {m n : ℕ} (h : m = n) :
    eqToHom (congrArg (fun k : ℕ ↦
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X (-(k : ℤ))) h) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A n).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A m).hom ≫
      (E).map (eqToHom (congrArg (fun k ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).X k) h)) := by
  cases h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using!
    (congrArg (fun f ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A m).hom ≫ f)
      ((E).map_id ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).X m))).symm
lemma simplicialRingDGCochainNegativeProduct_left_unit
    (A : SimplicialObject RingCat.{u}) (q : ℕ)
    (y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X (-(q : ℤ))) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A 0 q).hom
      (TensorProduct.tmul _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainOne A) y) =
    (eqToHom (congrArg (fun k : ℕ ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X (-(k : ℤ)))
      (Nat.zero_add q).symm)).hom y := by
  apply (ModuleCat.mono_iff_injective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A (0 + q)).hom).mp
    (by infer_instance)
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct_value A 0 q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainOne A) y
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainOne_degreeIso,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct_left_unit] at h
  have hc := congrArg (fun f ↦ f.hom y)
    (simplicialRingDGCochainDegreeIso_transport A (Nat.zero_add q).symm)
  exact h.trans hc.symm
lemma simplicialRingDGCochainNegativeProduct_assoc
    (A : SimplicialObject RingCat.{u}) (p q r : ℕ)
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X (-(p : ℤ)))
    (y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X (-(q : ℤ)))
    (z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X (-(r : ℤ))) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A (p + q) r).hom
      (TensorProduct.tmul _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A p q).hom
          (TensorProduct.tmul _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient x y)) z) =
    (eqToHom (congrArg (fun k : ℕ ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X (-(k : ℤ)))
      (Nat.add_assoc p q r).symm)).hom
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A p (q + r)).hom
        (TensorProduct.tmul _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient x
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A q r).hom
            (TensorProduct.tmul _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient y z)))) := by
  apply (ModuleCat.mono_iff_injective
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A ((p + q) + r)).hom).mp (by infer_instance)
  have hL := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct_value A (p + q) r
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A p q).hom
      (TensorProduct.tmul _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient x y)) z
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct_value A p q x y] at hL
  have hR := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct_value A p (q + r) x
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A q r).hom
      (TensorProduct.tmul _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient y z))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct_value A q r y z] at hR
  have hc := congrArg (fun f ↦ f.hom
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A p (q + r)).hom
      (TensorProduct.tmul _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient x
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A q r).hom
          (TensorProduct.tmul _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient y z)))))
    (simplicialRingDGCochainDegreeIso_transport A (Nat.add_assoc p q r).symm)
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct_assoc A p q r
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A p).hom.hom x)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A q).hom.hom y)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A r).hom.hom z)
  exact hL.trans (h.trans ((congrArg
    (eqToHom (congrArg (fun k ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).X k)
      (Nat.add_assoc p q r).symm)).hom hR.symm).trans hc.symm))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
