module


public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# 単体集合の二重写像円筒

概要：span A←C→B の二重写像円筒を実際の単体集合の pushout として構成する。
方針：C の円筒の両端を A と B に貼り付ける。
規約：Segal 1974 Lemma 1.7 の二重写像円筒の単体集合の模型。
使われ方：homotopy-cartesian な span の貼り合わせの比較射。

対応節は Kerodon 3.4（Tag 0106）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
end SerrePositivity.KST.Comparison
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares
open _root_.SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open scoped _root_.Simplicial

/--
概要：円筒の両端の包含を一つの射へまとめる。
方針：零端点と一端点から余積の普遍性で射を作る。
規約：Segal Lemma 1.7 の二重写像円筒の貼り付けの脚。
使われ方：実際の pushout の定義。
-/
def cylinderEndpoints (C : SSet.{u}) : C ⨿ C ⟶ C ⊗ Δ[1] :=
  coprod.desc SSet.ι₀ SSet.ι₁

/--
概要：span の二重写像円筒。
方針：両端点の円筒への射と、両端の対象への射を pushout する。
規約：A←C→B の向きで f:C→A、g:C→B を使う。
使われ方：Segal Lemma 1.7 の貼り合わせ先の実対象。
-/
def doubleMappingCylinder {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) : SSet.{u} :=
  pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (coprod.map f g)

/--
概要：二重写像円筒への中央の円筒の包含。
方針：pushout の第一の包含を使う。
規約：Segal Lemma 1.7 の円筒の部分。
使われ方：端点の貼り付けの式と span の射の誘導写像。
-/
def doubleMappingCylinder_middle {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) :
    C ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f g :=
  pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (coprod.map f g)

/--
概要：二重写像円筒への左の対象の包含。
方針：余積への包含と pushout の第二の包含を合成する。
規約：円筒の零端点を貼り付ける対象。
使われ方：左の頂点から貼り合わせ先への比較正方形。
-/
def doubleMappingCylinder_left {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f g :=
  coprod.inl ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (coprod.map f g)

/--
概要：二重写像円筒への右の対象の包含。
方針：余積への包含と pushout の第二の包含を合成する。
規約：円筒の一端点を貼り付ける対象。
使われ方：右の頂点から貼り合わせ先への比較正方形。
-/
def doubleMappingCylinder_right {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) :
    B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f g :=
  coprod.inr ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (coprod.map f g)

/--
概要：円筒の零端点は span の左の射で貼り付けられる。
方針：pushout の可換性を余積の左の包含で前合成する。
規約：Segal Lemma 1.7 の二重写像円筒の境界条件。
使われ方：span の射からの誘導写像の定義。
-/
@[reassoc] theorem doubleMappingCylinder_zero {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) :
    SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f g := by
  have h := congrArg (fun q => coprod.inl ≫ q)
    (pushout.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (g := coprod.map f g))
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints, coprod.inl_desc_assoc, coprod.inl_map_assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left, Category.assoc] using h

/--
概要：円筒の一端点は span の右の射で貼り付けられる。
方針：pushout の可換性を余積の右の包含で前合成する。
規約：Segal Lemma 1.7 の二重写像円筒の境界条件。
使われ方：span の射からの誘導写像の定義。
-/
@[reassoc] theorem doubleMappingCylinder_one {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) :
    SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f g := by
  have h := congrArg (fun q => coprod.inr ≫ q)
    (pushout.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) (g := coprod.map f g))
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints, coprod.inr_desc_assoc, coprod.inr_map_assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right, Category.assoc] using h

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
