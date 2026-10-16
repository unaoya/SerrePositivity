module
public import SerrePositivity.DifferentialGraded.Bimodule.TensorModuleMaps
public import SerrePositivity.DifferentialGraded.Bimodule.ValueExt

/-! # 積dg圏上の加群から主bimodule圏への射・評価を保つ関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

def map {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) :
    BimoduleCategory.of A B C (underlying A B C M).toBimodule ⟶
      BimoduleCategory.of A B C (underlying A B C N).toBimodule :=
  ⟨rightMap A B C f, rightMap_left_naturality A B C f⟩

@[simp]
lemma map_value {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map (map A B C f) =
      (leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c)).map f :=
  rightMap_component A B C f b c

lemma map_id (M : BimoduleTensorModuleCategory A B C) :
    map A B C (𝟙 M) = 𝟙 (BimoduleCategory.of A B C (underlying A B C M).toBimodule) := by
  apply BimoduleCategory.value_hom_ext A B C
  intro b c
  rw [map_value, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

lemma map_comp {M N P : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) (g : N ⟶ P) :
    map A B C (f ≫ g) = map A B C f ≫ map A B C g := by
  apply BimoduleCategory.value_hom_ext A B C
  intro b c
  rw [map_value, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    map_value, map_value]

/-- 射が両作用に全Hom自然であることを保持した、実際の閉零圏間の関手。 -/
def functor : BimoduleTensorModuleCategory A B C ⥤ BimoduleCategory A B C where
  obj M := BimoduleCategory.of A B C (underlying A B C M).toBimodule
  map := map A B C
  map_id := map_id A B C
  map_comp := map_comp A B C

@[simp]
lemma functor_map_value {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) (b : B) (c : C) :
    (BimoduleCategory.valueEvaluation A B C b c).map ((functor A B C).map f) =
      (leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c)).map f := map_value A B C f b c

/-- 各対象での複体の評価は、積dg圏上の元の評価に自然同型として一致する。 -/
def evaluationIso (b : B) (c : C) :
    functor A B C ⋙ BimoduleCategory.valueEvaluation A B C b c ≅
      leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c) :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun f => by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact map_value A B C f b c)

instance faithful : (functor A B C).Faithful where
  map_injective {M N} {f g} h := by
    apply leftModuleMorphism_ext A (DGTensorCategory A Bᵒᵖ C)
    intro x
    rcases x with ⟨b, c⟩
    have hh := congrArg (fun a => (BimoduleCategory.valueEvaluation A B C b.unop c).map a) h
    rw [functor_map_value, functor_map_value] at hh
    exact hh

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
