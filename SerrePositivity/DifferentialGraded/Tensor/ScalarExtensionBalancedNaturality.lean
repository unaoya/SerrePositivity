module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionBalanced
public import SerrePositivity.DifferentialGraded.Tensor.Maps

/-! # 相対 tensor の係数変更同型の両変数自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M M' : RightModule A D} {N N' : LeftModule A D}

omit [Small.{u} D] in
lemma extended_rightAction_family
    (f : ∀ x : D, M.obj (op x) ⟶ M'.obj (op x))
    (hf : ∀ x y, BalancedTensor.rightAction A D M x y ≫ f x =
      (f y ⊗ₘ 𝟙 (homObject A D x y)) ≫ BalancedTensor.rightAction A D M' x y)
    (x y : DGBaseChange φ D) :
    BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M) x y ≫
        (extension φ).map (f x) =
      ((extension φ).map (f y) ⊗ₘ 𝟙 (homObject A' (DGBaseChange φ D) x y)) ≫
        BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M') x y := by
  apply (cancel_epi (tensorIso φ (M.obj (op y)) (homObject A D x y)).hom).1
  rw [← Category.assoc]
  erw [← rightAction_comparison φ D M x y]
  rw [← CategoryTheory.Functor.map_comp, hf, CategoryTheory.Functor.map_comp]
  erw [rightAction_comparison φ D M' x y]
  have ht := tensorIso_naturality_assoc φ (f y) (𝟙 (homObject A D x y))
    (BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M') x y)
  simp only [CategoryTheory.Functor.map_id] at ht
  convert ht using 1

omit [Small.{u} D] in
lemma extended_leftAction_family
    (g : ∀ x : D, N.obj x ⟶ N'.obj x)
    (hg : ∀ x y, BalancedTensor.leftAction A D N x y ≫ g y =
      (𝟙 (homObject A D x y) ⊗ₘ g x) ≫ BalancedTensor.leftAction A D N' x y)
    (x y : DGBaseChange φ D) :
    BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N) x y ≫
        (extension φ).map (g y) =
      (𝟙 (homObject A' (DGBaseChange φ D) x y) ⊗ₘ (extension φ).map (g x)) ≫
        BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N') x y := by
  apply (cancel_epi (tensorIso φ (homObject A D x y) (N.obj x)).hom).1
  rw [← Category.assoc]
  erw [← leftAction_comparison φ D N x y]
  rw [← CategoryTheory.Functor.map_comp, hg, CategoryTheory.Functor.map_comp]
  erw [leftAction_comparison φ D N' x y]
  have ht := tensorIso_naturality_assoc φ (𝟙 (homObject A D x y)) (g x)
    (BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N') x y)
  simp only [CategoryTheory.Functor.map_id] at ht
  convert ht using 1

@[reassoc]
lemma balancedIso_naturality
    (f : ∀ x : D, M.obj (op x) ⟶ M'.obj (op x))
    (g : ∀ x : D, N.obj x ⟶ N'.obj x)
    (hf : ∀ x y, BalancedTensor.rightAction A D M x y ≫ f x =
      (f y ⊗ₘ 𝟙 (homObject A D x y)) ≫ BalancedTensor.rightAction A D M' x y)
    (hg : ∀ x y, BalancedTensor.leftAction A D N x y ≫ g y =
      (𝟙 (homObject A D x y) ⊗ₘ g x) ≫ BalancedTensor.leftAction A D N' x y) :
    (extension φ).map (BalancedTensor.mapOfFamilies A D f g hf hg) ≫
        (balancedIso φ D M' N').hom =
      (balancedIso φ D M N).hom ≫
        BalancedTensor.mapOfFamilies A' (DGBaseChange φ D)
          (M := rightModule φ D M) (M' := rightModule φ D M')
          (N := leftModule φ D N) (N' := leftModule φ D N')
          (fun x => (extension φ).map (f x)) (fun x => (extension φ).map (g x))
          (extended_rightAction_family φ D f hf) (extended_leftAction_family φ D g hg) := by
  apply extendedBalanced_hom_ext φ D M N
  intro x
  rw [← CategoryTheory.Functor.map_comp_assoc, BalancedTensor.ι_mapOfFamilies,
    CategoryTheory.Functor.map_comp, Category.assoc, balancedIso_ι,
    balancedIso_ι_assoc, BalancedTensor.ι_mapOfFamilies]
  exact tensorIso_naturality_assoc φ (f x) (g x) _

end SerrePositivity.DifferentialGraded.ScalarExtension
