module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingDGAlgebra
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory HomologicalComplex
open AlgebraicTopology AlgebraicTopology.DoldKan
open scoped TensorProduct _root_.Simplicial
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientModuleFunctor
lemma simplicialRingCoefficientMooreBidegree_naturality
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    (p q n : ℕ) (h : p + q = n) :
    ((E).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f).f p) ⊗ₘ
      (E).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f).f q)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree B p q n h =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree A p q n h ≫
        (E).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f).f n) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientTensorComparison_precomp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingMooreMultiplicationBidegree_naturality, Functor.map_comp]
  simp only [Category.assoc]
lemma simplicialRingDGCochainMooreBidegree_naturality
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    (p q n : ℕ) (h : p + q = n) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f).f (-(p : ℤ)) ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f).f (-(q : ℤ))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree B p q n h =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree A p q n h ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f).f (-(n : ℤ)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap_degree,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.tensorArrowConjugate]
  simp only [← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [← Category.assoc _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree B p q n h),
    simplicialRingCoefficientMooreBidegree_naturality, Category.assoc]
lemma simplicialRingDGCochainMultiplication_naturality
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    cochainTensorMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication B =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication A ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  by_cases hi : 0 < i
  · exact (Functor.map_isZero (tensorRight ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X j))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex_positive_zero A i hi)).eq_of_src _ _
  by_cases hj : 0 < j
  · exact (Functor.map_isZero (tensorLeft ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X i))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex_positive_zero A j hj)).eq_of_src _ _
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
  have hn : n = -((p + q : ℕ) : ℤ) := by omega
  cases hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication B).f _
    ((cochainTensorMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f)).f _
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A) _ _ _ hij (x ⊗ₜ[_] y))) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f).f _
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication A).f _
        (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A) _ _ _ hij (x ⊗ₜ[_] y)))
  rw [cochainTensorMap_apply_ι,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication_apply_negative,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication_apply_negative]
  exact congrArg (fun ψ ↦ ψ.hom (x ⊗ₜ[_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient] y))
    (simplicialRingDGCochainMooreBidegree_naturality f p q (p + q) rfl)
lemma simplicialRingNormalizedMap_one {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f).f 0).hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedOne A) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedOne B := by
  have h := congrArg (fun ψ ↦ (ψ.f 0).hom (1 : A.obj (Opposite.op ⦋0⦌)))
    (PInftyToNormalizedMooreComplex_naturality (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModuleMap f))
  have hf : ((AlternatingFaceMapComplex.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModuleMap f)).f 0).hom
      (1 : A.obj (Opposite.op ⦋0⦌)) = (1 : B.obj (Opposite.op ⦋0⦌)) :=
    (f.app (Opposite.op ⦋0⦌)).hom.map_one
  simpa only [comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedOne, hf] using! h.symm
lemma simplicialRingDGCochainMap_one {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f).f 0).hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainOne A) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainOne B := by
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap_degree f 0]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso B 0).inv.hom
    (((E).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f).f 0)).hom
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A 0).hom.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainOne A))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainOne_degreeIso]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso B 0).inv.hom
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f).f 0).hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedOne A)) = _
  rw [simplicialRingNormalizedMap_one]
  rfl
lemma simplicialRingDGCochainUnit_naturality {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainUnit A ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainUnit B := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [comp_f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainUnit_f_zero]
  simp only [Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMap f).f 0).hom
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainUnitArrow A).hom 1) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainUnitArrow B).hom 1
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainUnitArrow_one, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainUnitArrow_one,
    simplicialRingDGCochainMap_one]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
