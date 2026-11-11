module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModelUnitLoopEvaluation
/-! # 実単位閉路の全正方形と元四面体の二射影面

概要：実閉路を導来 nerve の全正方形へ評価し、元四面体の二射影面へ厳密に因子分解する。
方針：写像空間の uncurry の自然性と幾何的単位面の再添字を接続する。
規約：実閉路・元入力・元四面体と全時間を変更しない。
使われ方：D の単位退化と F1B の相対比較を指定した実閉路へ適用する。
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
local notation "I" => (Δ[1] : SSet)

lemma dgGluingModelRightUnitLoop_evaluate :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelRightUnitLoop R C D M X Y).h =
      (I ◁ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv ▷ I)) ≫
        (I ◁ (β_ P I).hom) ≫ (I ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelRightUnitLoop_h R C D M X Y]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapIntervalTriangle_evaluate]

lemma dgGluingModelLeftUnitLoop_evaluate :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelLeftUnitLoop R C D M X Y).h =
      (I ◁ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv ▷ I)) ≫
        (I ◁ (β_ P I).hom) ≫ (I ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily R C D M X Y 2 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelLeftUnitLoop_h R C D M X Y]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapIntervalTriangle_evaluate]

lemma dgGluingModelRightUnitLoop_tetrahedron_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelRightUnitLoop R C D M X Y).h =
      (I ◁ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv ▷ I)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTerminalUnitConeFamily P ≫ (stdSimplex.δ (1 : Fin 4) ▷ P) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[3] ⊗ P) ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
  rw [dgGluingModelRightUnitLoop_evaluate R C D M X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_first_unit P]

lemma dgGluingModelLeftUnitLoop_tetrahedron_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelLeftUnitLoop R C D M X Y).h =
      (I ◁ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv ▷ I)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingInitialUnitConeFamily P ≫ (stdSimplex.δ (2 : Fin 4) ▷ P) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[3] ⊗ P) ≫
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizationAugmentationTetrahedron R C D M X Y := by
  rw [dgGluingModelLeftUnitLoop_evaluate R C D M X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapPastingTriangleFamily,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_last_unit P]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
