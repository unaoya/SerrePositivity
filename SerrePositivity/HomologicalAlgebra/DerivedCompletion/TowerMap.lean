module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionQuasiIso
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerCoordinates
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleConeNaturality

/-! # 任意の複体塔の射によるホモトピー逆極限の写像

段ごとの同型に限定せず、任意の両立する射を差分の錐とシフトへ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable (R : Type u) [CommRing R]
variable {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (g : ∀ n, K n ⟶ L n) (hg : ∀ n, t n ≫ g n = g (n + 1) ≫ s n)

/-- 塔の任意の射を、直積上の差分のArrow射へ移す。 -/
def complexTowerDifferenceArrowMap :
    Arrow.mk (complexTowerDifference R K t) ⟶ Arrow.mk (complexTowerDifference R L s) :=
  Arrow.homMk (complexTowerProductMap R g) (complexTowerProductMap R g)
    (complexTowerDifference_naturality R t s g hg)

/-- 任意の両立する射は、具体的なholimモデルの射を与える。 -/
def complexTowerHomotopyLimitMap :
    complexTowerHomotopyLimit R K t ⟶ complexTowerHomotopyLimit R L s :=
  ((cochainMappingConeFunctor R).map (complexTowerDifferenceArrowMap R t s g hg))⟦(-1 : ℤ)⟧'

/-- 直積の各項の写像を成分ごとに計算する。 -/
theorem complexProductDegreeEquiv_map (i : ℤ) (x : (piObj K).X i) (k : ℕ) :
    complexProductDegreeEquiv R L i ((complexTowerProductMap R g).f i x) k =
      (g k).f i (complexProductDegreeEquiv R K i x k) := by
  simp only [complexProductDegreeEquiv_apply]
  exact congrArg (fun f ↦ (f.f i).hom x) (complexTowerProductMap_projection R g k)

/-- holimの射とシフトの各項の同型は可換する。 -/
theorem complexTowerHomotopyLimitDegreeIso_map (m n : ℤ) (h : m + 1 = n)
    (x : (complexTowerHomotopyLimit R K t).X n) :
    (CochainComplex.shiftFunctorObjXIso
      (CochainComplex.mappingCone (complexTowerDifference R L s)) (-1) n m (by omega)).hom
        ((complexTowerHomotopyLimitMap R t s g hg).f n x) =
      ((cochainMappingConeFunctor R).map (complexTowerDifferenceArrowMap R t s g hg)).f m
        ((CochainComplex.shiftFunctorObjXIso
          (CochainComplex.mappingCone (complexTowerDifference R K t))
          (-1) n m (by omega)).hom x) := by
  have hm : m = n + (-1) := by omega
  subst m
  simp [complexTowerHomotopyLimitMap, CochainComplex.shiftFunctorObjXIso]
  rfl

/-- holimの射の第1成分は、同じ次数の段ごとの射。 -/
theorem complexTowerHomotopyLimitDegreeEquiv_map_fst (m n : ℤ) (h : m + 1 = n)
    (x : (complexTowerHomotopyLimit R K t).X n) (k : ℕ) :
    (complexTowerHomotopyLimitDegreeEquiv R L s m n h
      ((complexTowerHomotopyLimitMap R t s g hg).f n x)).1 k =
        (g k).f n ((complexTowerHomotopyLimitDegreeEquiv R K t m n h x).1 k) := by
  rw [complexTowerHomotopyLimitDegreeEquiv_fst, complexTowerHomotopyLimitDegreeEquiv_fst,
    complexTowerHomotopyLimitDegreeIso_map R t s g hg m n h]
  let y := (CochainComplex.shiftFunctorObjXIso
    (CochainComplex.mappingCone (complexTowerDifference R K t)) (-1) n m (by omega)).hom x
  have hh := congrArg (fun f ↦ f.hom y)
    (moduleConeArrowMap_fst (complexTowerDifference R K t) (complexTowerDifference R L s)
      (complexTowerDifferenceArrowMap R t s g hg) m n h)
  change homotopyCofiber.fstX (complexTowerDifference R L s) m n h
      (((cochainMappingConeFunctor R).map
        (complexTowerDifferenceArrowMap R t s g hg)).f m y) =
    (complexTowerProductMap R g).f n
      (homotopyCofiber.fstX (complexTowerDifference R K t) m n h y) at hh
  rw [hh, complexProductDegreeEquiv_map]

/-- holimの射の第2成分は、一つ前の次数の段ごとの射。 -/
theorem complexTowerHomotopyLimitDegreeEquiv_map_snd (m n : ℤ) (h : m + 1 = n)
    (x : (complexTowerHomotopyLimit R K t).X n) (k : ℕ) :
    (complexTowerHomotopyLimitDegreeEquiv R L s m n h
      ((complexTowerHomotopyLimitMap R t s g hg).f n x)).2 k =
        (g k).f m ((complexTowerHomotopyLimitDegreeEquiv R K t m n h x).2 k) := by
  rw [complexTowerHomotopyLimitDegreeEquiv_snd, complexTowerHomotopyLimitDegreeEquiv_snd,
    complexTowerHomotopyLimitDegreeIso_map R t s g hg m n h]
  let y := (CochainComplex.shiftFunctorObjXIso
    (CochainComplex.mappingCone (complexTowerDifference R K t)) (-1) n m (by omega)).hom x
  have hh := congrArg (fun f ↦ f.hom y)
    (moduleConeArrowMap_snd (complexTowerDifference R K t) (complexTowerDifference R L s)
      (complexTowerDifferenceArrowMap R t s g hg) m)
  change homotopyCofiber.sndX (complexTowerDifference R L s) m
      (((cochainMappingConeFunctor R).map
        (complexTowerDifferenceArrowMap R t s g hg)).f m y) =
    (complexTowerProductMap R g).f m (homotopyCofiber.sndX (complexTowerDifference R K t) m y) at hh
  rw [hh, complexProductDegreeEquiv_map]

/-- 差分を消す標準持ち上げは、塔の任意の両立する射と可換する。 -/
theorem complexTowerHomotopyLimitLift_map
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (α : P ⟶ piObj K) (hα : α ≫ complexTowerDifference R K t = 0)
    (β : P ⟶ piObj L) (hβ : β ≫ complexTowerDifference R L s = 0)
    (hαβ : α ≫ complexTowerProductMap R g = β) :
    complexTowerHomotopyLimitLift R K t P α hα ≫
      complexTowerHomotopyLimitMap R t s g hg =
        complexTowerHomotopyLimitLift R L s P β hβ := by
  dsimp only [complexTowerHomotopyLimitMap]
  open CochainComplex.HomComplex in
  apply (Cocycle.equivHomShift (K := P)
    (L := CochainComplex.mappingCone (complexTowerDifference R L s)) (n := (-1 : ℤ))).injective
  rw [CochainComplex.HomComplex.Cocycle.equivHomShift_comp_shift (n := (-1 : ℤ))]
  apply Subtype.ext
  simp only [complexTowerHomotopyLimitLift,
    CochainComplex.HomComplex.Cocycle.postcomp, CochainComplex.HomComplex.Cocycle.mk_coe]
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp only [CochainComplex.mappingCone.liftCocycle_coe,
    CochainComplex.HomComplex.Cocycle.ofHom_coe, CochainComplex.mappingCone.liftCochain,
    CochainComplex.HomComplex.Cochain.zero_comp, add_zero]
  rw [CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [cochainMappingConeFunctor_inl]
  simp only [← CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [← CochainComplex.HomComplex.Cochain.ofHom_comp]
  change (CochainComplex.HomComplex.Cochain.ofHom
    (α ≫ complexTowerProductMap R g)).comp _ _ = _
  rw [hαβ]
  rfl

/-- 各段への両立する標準射の持ち上げと、holimの射の比較。 -/
theorem complexTowerCompatibleLift_map (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (α : ∀ n, P ⟶ K n) (hα : ∀ n, α (n + 1) ≫ t n = α n)
    (β : ∀ n, P ⟶ L n) (hβ : ∀ n, β (n + 1) ≫ s n = β n)
    (hαβ : ∀ n, α n ≫ g n = β n) :
    complexTowerCompatibleLift R K t P α hα ≫
      complexTowerHomotopyLimitMap R t s g hg = complexTowerCompatibleLift R L s P β hβ := by
  apply complexTowerHomotopyLimitLift_map
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, complexTowerProductMap_projection, ← Category.assoc,
    Pi.lift_comp_π, Pi.lift_comp_π, hαβ]

end SerrePositivity.DerivedCompletion
