module
public import SerrePositivity.DifferentialGraded.Bimodule.TensorModuleComparison
public import SerrePositivity.DifferentialGraded.Bimodule.UncurryNaturality
public import Mathlib.CategoryTheory.Equivalence

/-! # 積dg圏上の加群とbimoduleの閉零圏の同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma preimage_naturality {M N : BimoduleTensorModuleCategory A B C}
    (a : (functor A B C).obj M ⟶ (functor A B C).obj N)
    (x y : DGTensorCategory A Bᵒᵖ C) :
    (underlying A B C M).map x y ≫
      homPostcompose ((underlying A B C M).obj x)
        ((BimoduleCategory.valueEvaluation A B C y.1.unop y.2).map a) =
    (underlying A B C N).map x y ≫
      homPrecompose ((BimoduleCategory.valueEvaluation A B C x.1.unop x.2).map a)
        ((underlying A B C N).obj y) := by
  have h := BimoduleCategory.valueMap_uncurry_naturality A B C a x y
  change (underlying A B C M).toBimodule.toTensorFunctor.map x y ≫
      homPostcompose ((underlying A B C M).obj x)
        ((BimoduleCategory.valueEvaluation A B C y.1.unop y.2).map a) =
    (underlying A B C N).toBimodule.toTensorFunctor.map x y ≫
      homPrecompose ((BimoduleCategory.valueEvaluation A B C x.1.unop x.2).map a)
        ((underlying A B C N).obj y) at h
  have hm (F : BimoduleTensorFunctor A B C) :
      F.toBimodule.toTensorFunctor.map x y = F.map x y := by
    apply tensorHom_ext
    intro p q n hn
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f g
    change (F.toBimodule.uncurryHom x y).f n (dgTensorElement A f g hn) =
      (F.map x y).f n (dgTensorElement A f g hn)
    have hl := congrArg (fun t => t.f q g) (F.toBimodule_map_π x.2 y.2 y.1.unop)
    change F.toBimodule.leftCochain g y.1.unop =
      ((F.leftAt y.1.unop).map x.2 y.2).f q g at hl
    rw [Bimodule.uncurryHom_apply, hl, BimoduleTensorFunctor.map_tensorElement]
    rfl
  rw [hm, hm] at h
  exact h

/-- 両作用に全Hom自然なbimodule射を積dg圏上の加群射へ戻す。 -/
def preimageMap {M N : BimoduleTensorModuleCategory A B C}
    (a : (functor A B C).obj M ⟶ (functor A B C).obj N) : M ⟶ N :=
  leftModuleMorphismMk A (DGTensorCategory A Bᵒᵖ C)
    (M := underlying A B C M) (N := underlying A B C N)
    (fun x => (BimoduleCategory.valueEvaluation A B C x.1.unop x.2).map a)
    (preimage_naturality A B C a)

@[simp]
lemma preimageMap_eval {M N : BimoduleTensorModuleCategory A B C}
    (a : (functor A B C).obj M ⟶ (functor A B C).obj N)
    (x : DGTensorCategory A Bᵒᵖ C) :
    (leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) x).map (preimageMap A B C a) =
      (BimoduleCategory.valueEvaluation A B C x.1.unop x.2).map a :=
  leftModuleMorphismMk_eval A (DGTensorCategory A Bᵒᵖ C) _ _ x

@[simp]
lemma map_preimageMap {M N : BimoduleTensorModuleCategory A B C}
    (a : (functor A B C).obj M ⟶ (functor A B C).obj N) :
    (functor A B C).map (preimageMap A B C a) = a := by
  apply BimoduleCategory.value_hom_ext A B C
  intro b c
  rw [functor_map_value, preimageMap_eval]

@[simp]
lemma preimageMap_map {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) :
    preimageMap A B C ((functor A B C).map f) = f := by
  apply (functor A B C).map_injective
  exact map_preimageMap A B C _

lemma preimageMap_quasiIso_iff {M N : BimoduleTensorModuleCategory A B C}
    (a : (functor A B C).obj M ⟶ (functor A B C).obj N) :
    leftModuleQuasiIso A (DGTensorCategory A Bᵒᵖ C) (preimageMap A B C a) ↔
      BimoduleCategory.quasiIso A B C a := by
  rw [← functor_quasiIso_iff, map_preimageMap]

instance full : (functor A B C).Full where
  map_surjective a := ⟨preimageMap A B C a, map_preimageMap A B C a⟩

instance isEquivalence : (functor A B C).IsEquivalence where
  faithful := faithful A B C
  full := full A B C

/-- 対象だけでなく、全Hom自然な閉零射も含む圏同値。 -/
def equivalence : BimoduleTensorModuleCategory A B C ≌ BimoduleCategory A B C :=
  (functor A B C).asEquivalence

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
