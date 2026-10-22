module
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingDGMooreProduct
/-!
概要：実 cochain 負次数乗法と元の Moore 乗法の回収。
方針：元の実写像と係数環同型、次数移送を保持して比較する。
規約：単体環の可換性・対象宇宙の縮小を要求しない。使われ方：β5(g)。
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
def simplicialRingDGCochainDegreeIso (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    (simplicialRingNormalizedDGComplex A).X (-(n : ℤ)) ≅
      (E).obj ((simplicialRingNormalizedChains A).X n) :=
  (E).mapIso (simplicialRingCochainDegreeIso A n)


def simplicialRingDGCochainNegativeProduct (A : SimplicialObject RingCat.{u}) (p q : ℕ) :
    (simplicialRingNormalizedDGComplex A).X (-(p : ℤ)) ⊗
      (simplicialRingNormalizedDGComplex A).X (-(q : ℤ)) ⟶
        (simplicialRingNormalizedDGComplex A).X (-((p + q : ℕ) : ℤ)) :=
  ((simplicialRingDGCochainDegreeIso A p).hom ⊗ₘ
    (simplicialRingDGCochainDegreeIso A q).hom) ≫
      simplicialRingDGMooreDegreeProduct A p q ≫
        (simplicialRingDGCochainDegreeIso A (p + q)).inv

lemma simplicialRingDGCochainNegativeProduct_comp_degreeIso
    (A : SimplicialObject RingCat.{u}) (p q : ℕ) :
    simplicialRingDGCochainNegativeProduct A p q ≫
        (simplicialRingDGCochainDegreeIso A (p + q)).hom =
      ((simplicialRingDGCochainDegreeIso A p).hom ⊗ₘ
        (simplicialRingDGCochainDegreeIso A q).hom) ≫
          simplicialRingDGMooreDegreeProduct A p q := by
  simp only [simplicialRingDGCochainNegativeProduct, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]


lemma simplicialRingDGCochain_d (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    (simplicialRingNormalizedDGComplex A).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (simplicialRingDGCochainDegreeIso A (n + 1)).hom ≫
        (E).map ((simplicialRingNormalizedChains A).d (n + 1) n) ≫
          (simplicialRingDGCochainDegreeIso A n).inv := by
  change (E).map ((simplicialRingNormalizedCochain A).d _ _) = _
  rw [simplicialRingCochain_d, Functor.map_comp, Functor.map_comp]
  rfl

lemma simplicialRingDGCochainMap_degree {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) (n : ℕ) :
    (simplicialRingDGCochainMap f).f (-(n : ℤ)) =
      (simplicialRingDGCochainDegreeIso A n).hom ≫
        (E).map ((simplicialRingNormalizedMap f).f n) ≫
          (simplicialRingDGCochainDegreeIso B n).inv := by
  change (E).map ((simplicialRingCochainMap f).f _) = _
  rw [simplicialRingCochainMap_degree, Functor.map_comp, Functor.map_comp]
  rfl


lemma simplicialRingDGCochainNegativeProduct_value
    (A : SimplicialObject RingCat.{u}) (p q : ℕ)
    (x : (simplicialRingNormalizedDGComplex A).X (-(p : ℤ)))
    (y : (simplicialRingNormalizedDGComplex A).X (-(q : ℤ))) :
    (simplicialRingDGCochainDegreeIso A (p + q)).hom.hom
        ((simplicialRingDGCochainNegativeProduct A p q).hom
          (TensorProduct.tmul simplicialRingCoefficient x y)) =
      simplicialRingNormalizedDegreeProduct A p q
        ((simplicialRingDGCochainDegreeIso A p).hom.hom x)
        ((simplicialRingDGCochainDegreeIso A q).hom.hom y) := by
  have h := congrArg (fun f ↦ f.hom (TensorProduct.tmul simplicialRingCoefficient x y))
    (simplicialRingDGCochainNegativeProduct_comp_degreeIso A p q)
  change (simplicialRingDGCochainDegreeIso A (p + q)).hom.hom
      ((simplicialRingDGCochainNegativeProduct A p q).hom _) =
    (simplicialRingDGMooreDegreeProduct A p q).hom
      (TensorProduct.map (simplicialRingDGCochainDegreeIso A p).hom.hom
        (simplicialRingDGCochainDegreeIso A q).hom.hom _) at h
  rw [TensorProduct.map_tmul, simplicialRingDGMooreDegreeProduct_tmul] at h
  exact h


def simplicialRingDGCochainOne (A : SimplicialObject RingCat.{u}) :
    (simplicialRingNormalizedDGComplex A).X 0 :=
  (simplicialRingDGCochainDegreeIso A 0).inv.hom (simplicialRingNormalizedOne A)

lemma simplicialRingDGCochainOne_degreeIso (A : SimplicialObject RingCat.{u}) :
    (simplicialRingDGCochainDegreeIso A 0).hom.hom (simplicialRingDGCochainOne A) =
      simplicialRingNormalizedOne A := by
  exact congrArg (fun f ↦ f.hom (simplicialRingNormalizedOne A))
    (simplicialRingDGCochainDegreeIso A 0).inv_hom_id

lemma simplicialRingDGCochainNegativeProduct_right_unit
    (A : SimplicialObject RingCat.{u}) (p : ℕ)
    (x : (simplicialRingNormalizedDGComplex A).X (-(p : ℤ))) :
    (simplicialRingDGCochainNegativeProduct A p 0).hom
      (TensorProduct.tmul simplicialRingCoefficient x (simplicialRingDGCochainOne A)) = x := by
  apply (ModuleCat.mono_iff_injective (simplicialRingDGCochainDegreeIso A p).hom).mp
    (by infer_instance)
  have h := simplicialRingDGCochainNegativeProduct_value A p 0 x (simplicialRingDGCochainOne A)
  rw [simplicialRingDGCochainOne_degreeIso,
    simplicialRingNormalizedDegreeProduct_right_unit] at h
  exact h

end SerrePositivity.InfinityCategories
