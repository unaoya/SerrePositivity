module
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingDGAlgebra
/-!
概要：実正規化 cochain 乗法と単位の自然性。
方針：Moore 乗法の自然性を同じ次数同型と標準 tensor の外延性へ移す。
規約：可換性や平坦性を仮定しない。使われ方：β5(g) の正規化界面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory HomologicalComplex KST.ProExcision
open AlgebraicTopology AlgebraicTopology.DoldKan
open scoped TensorProduct Simplicial
local notation "E" => integerCoefficientModuleFunctor
lemma simplicialRingCoefficientMooreBidegree_naturality
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    (p q n : ℕ) (h : p + q = n) :
    ((E).map ((simplicialRingNormalizedMap f).f p) ⊗ₘ
      (E).map ((simplicialRingNormalizedMap f).f q)) ≫
        simplicialRingCoefficientMooreBidegree B p q n h =
      simplicialRingCoefficientMooreBidegree A p q n h ≫
        (E).map ((simplicialRingNormalizedMap f).f n) := by
  dsimp only [simplicialRingCoefficientMooreBidegree]
  rw [integerCoefficientTensorComparison_precomp,
    simplicialRingMooreMultiplicationBidegree_naturality, Functor.map_comp]
  simp only [Category.assoc]
lemma simplicialRingDGCochainMooreBidegree_naturality
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    (p q n : ℕ) (h : p + q = n) :
    ((simplicialRingDGCochainMap f).f (-(p : ℤ)) ⊗ₘ
      (simplicialRingDGCochainMap f).f (-(q : ℤ))) ≫
        simplicialRingDGCochainMooreBidegree B p q n h =
      simplicialRingDGCochainMooreBidegree A p q n h ≫
        (simplicialRingDGCochainMap f).f (-(n : ℤ)) := by
  simp only [simplicialRingDGCochainMap_degree,
    simplicialRingDGCochainMooreBidegree, tensorArrowConjugate]
  simp only [← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [← Category.assoc _ (simplicialRingCoefficientMooreBidegree B p q n h),
    simplicialRingCoefficientMooreBidegree_naturality, Category.assoc]
lemma simplicialRingDGCochainMultiplication_naturality
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    cochainTensorMap (simplicialRingDGCochainMap f) (simplicialRingDGCochainMap f) ≫
      simplicialRingDGCochainMultiplication B =
    simplicialRingDGCochainMultiplication A ≫ simplicialRingDGCochainMap f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  by_cases hi : 0 < i
  · exact (Functor.map_isZero (tensorRight ((simplicialRingNormalizedDGComplex A).X j))
      (simplicialRingNormalizedDGComplex_positive_zero A i hi)).eq_of_src _ _
  by_cases hj : 0 < j
  · exact (Functor.map_isZero (tensorLeft ((simplicialRingNormalizedDGComplex A).X i))
      (simplicialRingNormalizedDGComplex_positive_zero A j hj)).eq_of_src _ _
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
  have hn : n = -((p + q : ℕ) : ℤ) := by omega
  cases hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (simplicialRingDGCochainMultiplication B).f _
    ((cochainTensorMap (simplicialRingDGCochainMap f) (simplicialRingDGCochainMap f)).f _
      (ιTensorObj (simplicialRingNormalizedDGComplex A)
        (simplicialRingNormalizedDGComplex A) _ _ _ hij (x ⊗ₜ[_] y))) =
    (simplicialRingDGCochainMap f).f _
      ((simplicialRingDGCochainMultiplication A).f _
        (ιTensorObj (simplicialRingNormalizedDGComplex A)
        (simplicialRingNormalizedDGComplex A) _ _ _ hij (x ⊗ₜ[_] y)))
  rw [cochainTensorMap_apply_ι,
    simplicialRingDGCochainMultiplication_apply_negative,
    simplicialRingDGCochainMultiplication_apply_negative]
  exact congrArg (fun ψ ↦ ψ.hom (x ⊗ₜ[simplicialRingCoefficient] y))
    (simplicialRingDGCochainMooreBidegree_naturality f p q (p + q) rfl)
lemma simplicialRingNormalizedMap_one {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) :
    ((simplicialRingNormalizedMap f).f 0).hom (simplicialRingNormalizedOne A) =
      simplicialRingNormalizedOne B := by
  have h := congrArg (fun ψ ↦ (ψ.f 0).hom (1 : A.obj (Opposite.op ⦋0⦌)))
    (PInftyToNormalizedMooreComplex_naturality (simplicialRingIntegerModuleMap f))
  have hf : ((AlternatingFaceMapComplex.map (simplicialRingIntegerModuleMap f)).f 0).hom
      (1 : A.obj (Opposite.op ⦋0⦌)) = (1 : B.obj (Opposite.op ⦋0⦌)) :=
    (f.app (Opposite.op ⦋0⦌)).hom.map_one
  simpa only [comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    simplicialRingNormalizedOne, hf] using! h.symm
lemma simplicialRingDGCochainMap_one {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) :
    ((simplicialRingDGCochainMap f).f 0).hom (simplicialRingDGCochainOne A) =
      simplicialRingDGCochainOne B := by
  erw [simplicialRingDGCochainMap_degree f 0]
  change (simplicialRingDGCochainDegreeIso B 0).inv.hom
    (((E).map ((simplicialRingNormalizedMap f).f 0)).hom
      ((simplicialRingDGCochainDegreeIso A 0).hom.hom (simplicialRingDGCochainOne A))) = _
  rw [simplicialRingDGCochainOne_degreeIso]
  change (simplicialRingDGCochainDegreeIso B 0).inv.hom
    (((simplicialRingNormalizedMap f).f 0).hom (simplicialRingNormalizedOne A)) = _
  rw [simplicialRingNormalizedMap_one]
  rfl
lemma simplicialRingDGCochainUnit_naturality {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) :
    simplicialRingDGCochainUnit A ≫ simplicialRingDGCochainMap f =
      simplicialRingDGCochainUnit B := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [comp_f, simplicialRingDGCochainUnit_f_zero]
  simp only [Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change ((simplicialRingDGCochainMap f).f 0).hom
    ((simplicialRingDGCochainUnitArrow A).hom 1) =
      (simplicialRingDGCochainUnitArrow B).hom 1
  rw [simplicialRingDGCochainUnitArrow_one, simplicialRingDGCochainUnitArrow_one,
    simplicialRingDGCochainMap_one]
end SerrePositivity.InfinityCategories
