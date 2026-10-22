module
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingCoefficientComplex
public import SerrePositivity.DifferentialGraded.Complexes.Monoidal
/-!
概要：同宇宙の整数係数移送と実 tensor の自然同型。
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
abbrev integerCoefficientModuleFunctor :
    ModuleCat.{u} ℤ ⥤ ModuleCat.{u} simplicialRingCoefficient.{u} :=
  simplicialRingIntegerModuleEquivalence.{u}.functor
local notation "E" => integerCoefficientModuleFunctor


def integerCoefficientModuleDown (M : ModuleCat.{u} ℤ) :
    (E).obj M →ₛₗ[(ULift.ringEquiv : simplicialRingCoefficient.{u} ≃+* ℤ).toRingHom] M where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


def integerCoefficientTensorDown (M N : ModuleCat.{u} ℤ) :=
  TensorProduct.map (integerCoefficientModuleDown M) (integerCoefficientModuleDown N)


def integerCoefficientTensorDownAdd (M N : ModuleCat.{u} ℤ) :=
  (integerCoefficientTensorDown M N).toAddMonoidHom


attribute [-instance] ULift.module in
def integerCoefficientTensorComparison (M N : ModuleCat.{u} ℤ) :
    (E).obj M ⊗ (E).obj N ⟶ (E).obj (integerTensor M N) := by
  letI := ((E).obj M).isModule
  letI := ((E).obj N).isModule
  letI : Module simplicialRingCoefficient (integerTensor M N) :=
    ((E).obj (integerTensor M N)).isModule
  exact ModuleCat.ofHom
    { toFun := integerCoefficientTensorDownAdd M N
      map_add' := (integerCoefficientTensorDownAdd M N).map_add
      map_smul' := by
        intro r z
        rcases r with ⟨n⟩
        exact map_intCast_smul (integerCoefficientTensorDownAdd M N)
          simplicialRingCoefficient simplicialRingCoefficient n z }


lemma integerCoefficientTensorComparison_tmul (M N : ModuleCat.{u} ℤ) (x : M) (y : N) :
    (integerCoefficientTensorComparison M N).hom
      (TensorProduct.tmul simplicialRingCoefficient (M := (E).obj M) (N := (E).obj N) x y) =
      TensorProduct.tmul ℤ (M := M) (N := N) x y := rfl

lemma integerCoefficientTensorComparison_naturality {M M' N N' : ModuleCat.{u} ℤ}
    (f : M ⟶ M') (g : N ⟶ N') :
    ((E).map f ⊗ₘ (E).map g) ≫ integerCoefficientTensorComparison M' N' =
      integerCoefficientTensorComparison M N ≫ (E).map (integerTensorMap f g) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (integerCoefficientTensorComparison M' N').hom
      (TensorProduct.map ((E).map f).hom ((E).map g).hom
        (TensorProduct.tmul simplicialRingCoefficient x y)) =
    ((E).map (integerTensorMap f g)).hom
      ((integerCoefficientTensorComparison M N).hom
        (TensorProduct.tmul simplicialRingCoefficient x y))
  rw [TensorProduct.map_tmul, integerCoefficientTensorComparison_tmul,
    integerCoefficientTensorComparison_tmul]
  exact (TensorProduct.map_tmul f.hom g.hom x y).symm


def integerCoefficientModuleUp (M : ModuleCat.{u} ℤ) :
    M →ₛₗ[(ULift.ringEquiv : simplicialRingCoefficient.{u} ≃+* ℤ).symm.toRingHom]
      (E).obj M where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


def integerCoefficientTensorUp (M N : ModuleCat.{u} ℤ) :=
  TensorProduct.map (integerCoefficientModuleUp M) (integerCoefficientModuleUp N)

def integerCoefficientTensorUpAdd (M N : ModuleCat.{u} ℤ) :=
  (integerCoefficientTensorUp M N).toAddMonoidHom


attribute [-instance] ULift.module in
def integerCoefficientTensorComparisonInv (M N : ModuleCat.{u} ℤ) :
    (E).obj (integerTensor M N) ⟶ (E).obj M ⊗ (E).obj N := by
  letI := ((E).obj M).isModule
  letI := ((E).obj N).isModule
  letI : Module simplicialRingCoefficient (integerTensor M N) :=
    ((E).obj (integerTensor M N)).isModule
  exact ModuleCat.ofHom
    { toFun := integerCoefficientTensorUpAdd M N
      map_add' := (integerCoefficientTensorUpAdd M N).map_add
      map_smul' := by
        intro r z
        rcases r with ⟨n⟩
        exact map_intCast_smul (integerCoefficientTensorUpAdd M N)
          simplicialRingCoefficient simplicialRingCoefficient n z }

lemma integerCoefficientTensorComparisonInv_tmul (M N : ModuleCat.{u} ℤ) (x : M) (y : N) :
    (integerCoefficientTensorComparisonInv M N).hom (TensorProduct.tmul ℤ (M := M) (N := N) x y) =
      TensorProduct.tmul simplicialRingCoefficient (M := (E).obj M) (N := (E).obj N) x y := rfl


def integerCoefficientTensorIso (M N : ModuleCat.{u} ℤ) :
    (E).obj M ⊗ (E).obj N ≅ (E).obj (integerTensor M N) where
  hom := integerCoefficientTensorComparison M N
  inv := integerCoefficientTensorComparisonInv M N
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    refine TensorProduct.inductionOn z (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · rfl
    · simp only [map_add, hx, hy]

end SerrePositivity.InfinityCategories
