module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ProductCoordinates
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleConeCoordinates

/-! # 任意複体塔のholimの二成分表示と微分 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

variable (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (t : ∀ n, K (n + 1) ⟶ K n)

/-- holimの次数nの項を、次数nとmの列の組に同定する。 -/
def complexTowerHomotopyLimitDegreeEquiv (m n : ℤ) (h : m + 1 = n) :
    (complexTowerHomotopyLimit R K t).X n ≃ₗ[R]
      (∀ k, (K k).X n) × (∀ k, (K k).X m) :=
  (CochainComplex.shiftFunctorObjXIso
    (CochainComplex.mappingCone (complexTowerDifference R K t))
    (-1) n m (by omega)).toLinearEquiv ≪≫ₗ
    moduleConeDegreeEquiv (complexTowerDifference R K t) m n h ≪≫ₗ
      (complexProductDegreeEquiv R K n).prodCongr (complexProductDegreeEquiv R K m)

/-- 二成分表示の第1成分は、外側の錐の第1射影。 -/
theorem complexTowerHomotopyLimitDegreeEquiv_fst (m n : ℤ) (h : m + 1 = n)
    (x : (complexTowerHomotopyLimit R K t).X n) :
    (complexTowerHomotopyLimitDegreeEquiv R K t m n h x).1 =
      complexProductDegreeEquiv R K n
        (fstX (complexTowerDifference R K t) m n h
          ((CochainComplex.shiftFunctorObjXIso
            (CochainComplex.mappingCone (complexTowerDifference R K t))
            (-1) n m (by omega)).hom x)) := rfl

/-- 二成分表示の第2成分は、外側の錐の第2射影。 -/
theorem complexTowerHomotopyLimitDegreeEquiv_snd (m n : ℤ) (h : m + 1 = n)
    (x : (complexTowerHomotopyLimit R K t).X n) :
    (complexTowerHomotopyLimitDegreeEquiv R K t m n h x).2 =
      complexProductDegreeEquiv R K m
        (sndX (complexTowerDifference R K t) m
          ((CochainComplex.shiftFunctorObjXIso
            (CochainComplex.mappingCone (complexTowerDifference R K t))
            (-1) n m (by omega)).hom x)) := rfl

/-- シフトしたholimの微分を、外側の錐の微分へ移す。 -/
theorem complexTowerHomotopyLimitDegreeIso_d (m n p : ℤ)
    (h : m + 1 = n) (h' : n + 1 = p)
    (x : (complexTowerHomotopyLimit R K t).X n) :
    (CochainComplex.shiftFunctorObjXIso
            (CochainComplex.mappingCone (complexTowerDifference R K t)) (-1) p n (by omega)).hom
        ((complexTowerHomotopyLimit R K t).d n p x) =
      -((CochainComplex.mappingCone (complexTowerDifference R K t)).d m n
        ((CochainComplex.shiftFunctorObjXIso
          (CochainComplex.mappingCone (complexTowerDifference R K t))
          (-1) n m (by omega)).hom x)) := by
  have hm : m = n + (-1) := by omega
  have hn : n = p + (-1) := by omega
  subst m n
  simp [complexTowerHomotopyLimit, CochainComplex.shiftFunctorObjXIso]

/-- holimの二成分表示の第1成分の微分。 -/
theorem complexTowerHomotopyLimitDegreeEquiv_d_fst (m n p : ℤ)
    (h : m + 1 = n) (h' : n + 1 = p)
    (x : (complexTowerHomotopyLimit R K t).X n) (k : ℕ) :
    (complexTowerHomotopyLimitDegreeEquiv R K t n p h'
      ((complexTowerHomotopyLimit R K t).d n p x)).1 k =
        (K k).d n p ((complexTowerHomotopyLimitDegreeEquiv R K t m n h x).1 k) := by
  rw [complexTowerHomotopyLimitDegreeEquiv_fst, complexTowerHomotopyLimitDegreeEquiv_fst,
    complexTowerHomotopyLimitDegreeIso_d R K t m n p h h']
  let y := (CochainComplex.shiftFunctorObjXIso
    (CochainComplex.mappingCone (complexTowerDifference R K t)) (-1) n m (by omega)).hom x
  have hd := congrArg (fun f ↦ f.hom y)
    (d_fstX (complexTowerDifference R K t) m n p h h')
  change fstX (complexTowerDifference R K t) n p h'
      ((CochainComplex.mappingCone (complexTowerDifference R K t)).d m n y) =
    -((piObj K).d n p (fstX (complexTowerDifference R K t) m n h y)) at hd
  simp only [map_neg]
  rw [hd]
  simp only [map_neg, neg_neg, complexProductDegreeEquiv_d]
  rfl

/-- holimの第2成分の微分は、塔の差分と前の次数の微分の負の和。 -/
theorem complexTowerHomotopyLimitDegreeEquiv_d_snd (m n p : ℤ)
    (h : m + 1 = n) (h' : n + 1 = p)
    (x : (complexTowerHomotopyLimit R K t).X n) (k : ℕ) :
    (complexTowerHomotopyLimitDegreeEquiv R K t n p h'
      ((complexTowerHomotopyLimit R K t).d n p x)).2 k =
      -((complexTowerHomotopyLimitDegreeEquiv R K t m n h x).1 k -
          (t k).f n ((complexTowerHomotopyLimitDegreeEquiv R K t m n h x).1 (k + 1))) -
        (K k).d m n ((complexTowerHomotopyLimitDegreeEquiv R K t m n h x).2 k) := by
  rw [complexTowerHomotopyLimitDegreeEquiv_snd, complexTowerHomotopyLimitDegreeEquiv_fst,
    complexTowerHomotopyLimitDegreeEquiv_snd,
    complexTowerHomotopyLimitDegreeIso_d R K t m n p h h']
  let y := (CochainComplex.shiftFunctorObjXIso
    (CochainComplex.mappingCone (complexTowerDifference R K t)) (-1) n m (by omega)).hom x
  have hd := congrArg (fun f ↦ f.hom y)
    (d_sndX (complexTowerDifference R K t) m n h)
  change sndX (complexTowerDifference R K t) n
      ((CochainComplex.mappingCone (complexTowerDifference R K t)).d m n y) =
    (complexTowerDifference R K t).f n (fstX (complexTowerDifference R K t) m n h y) +
      (piObj K).d m n (sndX (complexTowerDifference R K t) m y) at hd
  simp only [map_neg]
  rw [hd]
  simp only [map_add, Pi.neg_apply, Pi.add_apply, complexProductDegreeEquiv_difference,
    complexProductDegreeEquiv_d, neg_add, sub_eq_add_neg]
  rfl

end SerrePositivity.DerivedCompletion
