module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.ModelUnitLoopRawEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.UnitConeFamilyReindex
/-! # 主経路四面体の二射影と実単位閉路

概要：元導来 augmentation 四面体の二射影を主経路の全入力上で保持し、実単位閉路を照合する。
方針：同じ Hom 模型同型の逆で入力を制限し、単位閉路の再添字の自然性を適用する。
規約：四面体や閉路を選び直さず、全正方形を厳密に回収する。
使われ方：二射影の単位面の退化を、③・④の残る二単位閉路へ供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedHomParameter R C D M X Y
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarParameter R C D M X Y

def dgGluingModelUnitProjectionTetrahedron (i : Fin 2) :=
  (Δ[3] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[3] ⊗ P) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y

lemma dgGluingModelRightUnitLoop_model_tetrahedron_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelRightUnitLoop R C D M X Y).h =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitConeFamily K ≫ (stdSimplex.δ (1 : Fin 4) ▷ K) ≫
        dgGluingModelUnitProjectionTetrahedron R C D M X Y 1 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelRightUnitLoop_tetrahedron_face R C D M X Y,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitConeFamily_face_naturality
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv (stdSimplex.δ (1 : Fin 4))]
  rfl

lemma dgGluingModelLeftUnitLoop_model_tetrahedron_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelLeftUnitLoop R C D M X Y).h =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily K ≫ (stdSimplex.δ (2 : Fin 4) ▷ K) ≫
        dgGluingModelUnitProjectionTetrahedron R C D M X Y 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelLeftUnitLoop_tetrahedron_face R C D M X Y,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily_face_naturality
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv (stdSimplex.δ (2 : Fin 4))]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
