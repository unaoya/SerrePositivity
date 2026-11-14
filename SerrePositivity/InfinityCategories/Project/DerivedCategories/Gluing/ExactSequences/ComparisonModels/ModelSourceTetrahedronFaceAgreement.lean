module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativeNormalizationProjectionFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.NormalizationSourceTetrahedron
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.ModelUnitLoopTetrahedronFaces
/-! # 主経路の始側四面体の二つの終側面の厳密一致

概要：元 replacement 射影の二面の一致を、同じ導来 augmentation 四面体と主経路へ移す。
方針：全単体族の宇宙輸送と同じ Hom 模型同型の逆だけで入力を制限する。
規約：単位則や新たな比較仮定を使わず、選択済み四面体を保持する。
使われ方：左単位面の相対内角比較で二面を無条件に固定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "E" => _root_.SerrePositivity.DifferentialGraded.RightModule R C
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M Y
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedHomParameter R C D M X Y
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCollarParameter R C D M X Y

lemma dgGluingNativeNormalizationRawTetrahedron_source_faces :
    (stdSimplex.δ (1 : Fin 4) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R Q IX IY) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[3] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R Q IX IY) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationRawTetrahedron R C D M X Y =
    (stdSimplex.δ (0 : Fin 4) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R Q IX IY) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[3] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R Q IX IY) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationRawTetrahedron R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationSourceTetrahedron_one_eq_zero.{u, max (u + 1) v} R E IX IY (𝟙 _)

lemma dgGluingNativeNormalizationAugmentationTetrahedron_source_faces :
    (stdSimplex.δ (1 : Fin 4) ▷ P) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[3] ⊗ P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y =
    (stdSimplex.δ (0 : Fin 4) ▷ P) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[3] ⊗ P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationSimplexPrism_endpoint,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationSimplexProjection_face]
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationSimplexProjection R C D M X Y 2)
    (dgGluingNativeNormalizationRawTetrahedron_source_faces R C D M X Y)

lemma dgGluingModelUnitProjectionTetrahedron_source_faces :
    (stdSimplex.δ (1 : Fin 4) ▷ K) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitProjectionTetrahedron R C D M X Y 0 =
    (stdSimplex.δ (0 : Fin 4) ▷ K) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitProjectionTetrahedron R C D M X Y 0 := by
  calc
    _ = (Δ[2] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv) ≫
        (stdSimplex.δ (1 : Fin 4) ▷ P) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[3] ⊗ P) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
      apply SSet.hom_ext
      intro m
      apply ConcreteCategory.hom_ext
      intro p
      rfl
    _ = (Δ[2] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv) ≫
        (stdSimplex.δ (0 : Fin 4) ▷ P) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[3] ⊗ P) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
      rw [dgGluingNativeNormalizationAugmentationTetrahedron_source_faces R C D M X Y]
    _ = _ := by
      apply SSet.hom_ext
      intro m
      apply ConcreteCategory.hom_ext
      intro p
      rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
