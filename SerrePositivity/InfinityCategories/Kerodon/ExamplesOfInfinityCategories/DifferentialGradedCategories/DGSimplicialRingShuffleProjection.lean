module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingShuffleDegeneracy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingShuffleNative
/-!
概要：実 shuffle 積の退化零化と正規化射影の整合性。
方針：共通退化因子・PInfty の補射影と元の実結合・単位を接続する。
規約：非可換な積の順序と元の全次数を保つ。使われ方：β5(g) の正規化 dg 代数化。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite AlgebraicTopology AlgebraicTopology.DoldKan
open EInfinity.BarrattEccles
open scoped _root_.Simplicial
def ringShuffleBilinear (A : SimplicialObject RingCat.{u}) (p q : ℕ) :
    A.obj (op ⦋p⦌) →ₗ[ℤ] A.obj (op ⦋q⦌) →ₗ[ℤ] A.obj (op ⦋p + q⦌) :=
  TensorProduct.curry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A) p q (p + q) rfl ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerMultiplication A).app (op ⦋p + q⦌)).hom
lemma ringShuffleBilinear_apply (A : SimplicialObject RingCat.{u}) (p q : ℕ)
    (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) :
    ringShuffleBilinear A p q x y = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p q x y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct_eq_shuffleBidegree A p q x y
def projectedRingShuffleBilinear (A : SimplicialObject RingCat.{u}) (p q : ℕ) :
    A.obj (op ⦋p⦌) →ₗ[ℤ] A.obj (op ⦋q⦌) →ₗ[ℤ] A.obj (op ⦋p + q⦌) :=
  TensorProduct.curry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A) p q (p + q) rfl ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerMultiplication A).app (op ⦋p + q⦌) ≫
        (PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + q)).hom
lemma projectedRingShuffleBilinear_apply (A : SimplicialObject RingCat.{u}) (p q : ℕ)
    (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) :
    projectedRingShuffleBilinear A p q x y =
      ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + q)).hom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p q x y) := by
  change ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + q)).hom
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A) p q (p + q) rfl ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerMultiplication A).app (op ⦋p + q⦌)).hom
          (TensorProduct.tmul ℤ x y)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct_eq_shuffleBidegree]
lemma projectedRingShuffleProduct_degenerate_left (A : SimplicialObject RingCat.{u})
    (p q : ℕ) (i : Fin (p + 1)) (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) :
    ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + 1 + q)).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A (p + 1) q ((A.σ i).hom x) y) = 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct, map_sum, map_zsmul]
  apply Finset.sum_eq_zero
  intro s _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringShuffleTerm_degenerate_left, smul_zero]
lemma projectedRingShuffleProduct_degenerate_right (A : SimplicialObject RingCat.{u})
    (p q : ℕ) (i : Fin (q + 1)) (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) :
    ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + (q + 1))).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p (q + 1) x ((A.σ i).hom y)) = 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct, map_sum, map_zsmul]
  apply Finset.sum_eq_zero
  intro s _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ringShuffleTerm_degenerate_right, smul_zero]
lemma projectedRingShuffleBilinear_left_degeneracies (A : SimplicialObject RingCat.{u})
    (p q : ℕ) (y : A.obj (op ⦋q⦌)) :
    DegeneraciesVanish (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)
      (ModuleCat.ofHom ((projectedRingShuffleBilinear A p q).flip y)) := by
  cases p with
  | zero =>
    rw [degeneraciesVanish_zero_iff_true]
    trivial
  | succ p =>
    rw [degeneraciesVanish_succ_iff]
    intro i
    apply ModuleCat.hom_ext
    ext x
    change projectedRingShuffleBilinear A (p + 1) q ((A.σ i).hom x) y = 0
    rw [projectedRingShuffleBilinear_apply, projectedRingShuffleProduct_degenerate_left]
lemma projectedRingShuffleBilinear_right_degeneracies (A : SimplicialObject RingCat.{u})
    (p q : ℕ) (x : A.obj (op ⦋p⦌)) :
    DegeneraciesVanish (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)
      (ModuleCat.ofHom (projectedRingShuffleBilinear A p q x)) := by
  cases q with
  | zero =>
    rw [degeneraciesVanish_zero_iff_true]
    trivial
  | succ q =>
    rw [degeneraciesVanish_succ_iff]
    intro i
    apply ModuleCat.hom_ext
    ext y
    change projectedRingShuffleBilinear A p (q + 1) x ((A.σ i).hom y) = 0
    rw [projectedRingShuffleBilinear_apply, projectedRingShuffleProduct_degenerate_right]
universe v w
lemma normalizedProjection_comp_of_degeneracies {V : Type v} [Category.{w} V] [Preadditive V]
    {X : SimplicialObject V} {n : ℕ} {T : V} (f : X.obj (op ⦋n⦌) ⟶ T)
    (hf : DegeneraciesVanish f) : (PInfty (X := X)).f n ≫ f = f := by
  have h := (degeneraciesVanish_iff_QInfty_f_comp f).mp hf
  change (𝟙 _ - (PInfty (X := X)).f n) ≫ f = 0 at h
  rw [Preadditive.sub_comp, Category.id_comp] at h
  exact (sub_eq_zero.mp h).symm
lemma projectedRingShuffleProduct_left_projection (A : SimplicialObject RingCat.{u})
    (p q : ℕ) (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) :
    ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + q)).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p q
        (((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f p).hom x) y) =
    ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + q)).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p q x y) := by
  have h := normalizedProjection_comp_of_degeneracies _
    (projectedRingShuffleBilinear_left_degeneracies A p q y)
  have hv := congrArg (fun f ↦ f.hom x) h
  change projectedRingShuffleBilinear A p q
    (((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f p).hom x) y =
      projectedRingShuffleBilinear A p q x y at hv
  simpa only [projectedRingShuffleBilinear_apply] using hv
lemma projectedRingShuffleProduct_right_projection (A : SimplicialObject RingCat.{u})
    (p q : ℕ) (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) :
    ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + q)).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p q x
        (((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f q).hom y)) =
    ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + q)).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p q x y) := by
  have h := normalizedProjection_comp_of_degeneracies _
    (projectedRingShuffleBilinear_right_degeneracies A p q x)
  have hv := congrArg (fun f ↦ f.hom y) h
  change projectedRingShuffleBilinear A p q x
    (((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f q).hom y) =
      projectedRingShuffleBilinear A p q x y at hv
  simpa only [projectedRingShuffleBilinear_apply] using hv
end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
