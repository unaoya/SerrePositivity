module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModelUnitCapTriangleDiagrams
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCapPastingCoefficientFace
/-! # 主経路の係数対角と同じ明示 augmentation prism

概要：係数片の対角を、主経路上の同じ明示 augmentation prism の辺へ同定する。
方針：元 Hom 模型同型の逆と順射を相殺し、正本端点表示を保持して curry する。
規約：全入力と全時間を保ち、別の係数 path を選ばない。
使われ方：両端固定正規化を使って指定係数対角辺へ高次貼り合わせを移す。
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

lemma dgGluingModelUnitCapTriangleDiagram_coefficient_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram R C D M X Y 4 =
      curry ((β_ K (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedAugmentationPrism R C D M X Y ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModelUnitCapTriangleDiagram, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCapIntervalTriangle_coefficient_diagonal R C D M X Y]
  apply congrArg curry
  have he : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv ▷ Δ[1]) ≫
      (β_ P (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y) =
      (β_ K (Δ[1] : SSet.{max (u + 1) v w})).hom := by
    calc
      _ = (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y) ▷ Δ[1]) ≫
          (β_ K (Δ[1] : SSet.{max (u + 1) v w})).hom := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro a
        rfl
      _ = _ := by
        rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso_hom R C D M X Y, Iso.inv_hom_id,
          id_whiskerRight, Category.id_comp]
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedAugmentationPrism R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) he
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
