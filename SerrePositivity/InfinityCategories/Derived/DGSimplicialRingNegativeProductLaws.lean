module
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingNegativeProduct
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
namespace SerrePositivity.InfinityCategories
open scoped TensorProduct
open CategoryTheory MonoidalCategory KST.ProExcision
local notation "E" => integerCoefficientModuleFunctor
lemma simplicialRingDGCochainDegreeIso_transport
    (A : SimplicialObject RingCat.{u}) {m n : ℕ} (h : m = n) :
    eqToHom (congrArg (fun k : ℕ ↦
        (simplicialRingNormalizedDGComplex A).X (-(k : ℤ))) h) ≫
      (simplicialRingDGCochainDegreeIso A n).hom =
    (simplicialRingDGCochainDegreeIso A m).hom ≫
      (E).map (eqToHom (congrArg (fun k ↦ (simplicialRingNormalizedChains A).X k) h)) := by
  cases h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using!
    (congrArg (fun f ↦ (simplicialRingDGCochainDegreeIso A m).hom ≫ f)
      ((E).map_id ((simplicialRingNormalizedChains A).X m))).symm
lemma simplicialRingDGCochainNegativeProduct_left_unit
    (A : SimplicialObject RingCat.{u}) (q : ℕ)
    (y : (simplicialRingNormalizedDGComplex A).X (-(q : ℤ))) :
    (simplicialRingDGCochainNegativeProduct A 0 q).hom
      (TensorProduct.tmul simplicialRingCoefficient (simplicialRingDGCochainOne A) y) =
    (eqToHom (congrArg (fun k : ℕ ↦ (simplicialRingNormalizedDGComplex A).X (-(k : ℤ)))
      (Nat.zero_add q).symm)).hom y := by
  apply (ModuleCat.mono_iff_injective (simplicialRingDGCochainDegreeIso A (0 + q)).hom).mp
    (by infer_instance)
  have h := simplicialRingDGCochainNegativeProduct_value A 0 q (simplicialRingDGCochainOne A) y
  rw [simplicialRingDGCochainOne_degreeIso,
    simplicialRingNormalizedDegreeProduct_left_unit] at h
  have hc := congrArg (fun f ↦ f.hom y)
    (simplicialRingDGCochainDegreeIso_transport A (Nat.zero_add q).symm)
  exact h.trans hc.symm
lemma simplicialRingDGCochainNegativeProduct_assoc
    (A : SimplicialObject RingCat.{u}) (p q r : ℕ)
    (x : (simplicialRingNormalizedDGComplex A).X (-(p : ℤ)))
    (y : (simplicialRingNormalizedDGComplex A).X (-(q : ℤ)))
    (z : (simplicialRingNormalizedDGComplex A).X (-(r : ℤ))) :
    (simplicialRingDGCochainNegativeProduct A (p + q) r).hom
      (TensorProduct.tmul simplicialRingCoefficient
        ((simplicialRingDGCochainNegativeProduct A p q).hom
          (TensorProduct.tmul simplicialRingCoefficient x y)) z) =
    (eqToHom (congrArg (fun k : ℕ ↦ (simplicialRingNormalizedDGComplex A).X (-(k : ℤ)))
      (Nat.add_assoc p q r).symm)).hom
      ((simplicialRingDGCochainNegativeProduct A p (q + r)).hom
        (TensorProduct.tmul simplicialRingCoefficient x
          ((simplicialRingDGCochainNegativeProduct A q r).hom
            (TensorProduct.tmul simplicialRingCoefficient y z)))) := by
  apply (ModuleCat.mono_iff_injective
    (simplicialRingDGCochainDegreeIso A ((p + q) + r)).hom).mp (by infer_instance)
  have hL := simplicialRingDGCochainNegativeProduct_value A (p + q) r
    ((simplicialRingDGCochainNegativeProduct A p q).hom
      (TensorProduct.tmul simplicialRingCoefficient x y)) z
  rw [simplicialRingDGCochainNegativeProduct_value A p q x y] at hL
  have hR := simplicialRingDGCochainNegativeProduct_value A p (q + r) x
    ((simplicialRingDGCochainNegativeProduct A q r).hom
      (TensorProduct.tmul simplicialRingCoefficient y z))
  rw [simplicialRingDGCochainNegativeProduct_value A q r y z] at hR
  have hc := congrArg (fun f ↦ f.hom
    ((simplicialRingDGCochainNegativeProduct A p (q + r)).hom
      (TensorProduct.tmul simplicialRingCoefficient x
        ((simplicialRingDGCochainNegativeProduct A q r).hom
          (TensorProduct.tmul simplicialRingCoefficient y z)))))
    (simplicialRingDGCochainDegreeIso_transport A (Nat.add_assoc p q r).symm)
  have h := simplicialRingNormalizedDegreeProduct_assoc A p q r
    ((simplicialRingDGCochainDegreeIso A p).hom.hom x)
    ((simplicialRingDGCochainDegreeIso A q).hom.hom y)
    ((simplicialRingDGCochainDegreeIso A r).hom.hom z)
  exact hL.trans (h.trans ((congrArg
    (eqToHom (congrArg (fun k ↦ (simplicialRingNormalizedChains A).X k)
      (Nat.add_assoc p q r).symm)).hom hR.symm).trans hc.symm))
end SerrePositivity.InfinityCategories
