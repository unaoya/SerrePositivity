module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyTetrahedra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackConeTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackConeHomotopy

/-!
概要：引き戻し錐の比較円柱の実際の三単体と上下・共有面。
方針：元の指定ホモトピーを各 cospan の射上の三角形に制限する。
規約：元と置換後の錐の三角形を厳密に回収する。
使われ方：四面の関手同型の合成則の引き戻し錐への適用。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：引き戻し錐の指定比較円柱を構成する三つの三単体。
方針：同じ全錐のホモトピーの標準三角形への制限を使う。
規約：三単体の充填を新しく選択しない。
使われ方：二脚の比較と native な可換性の同時照合。 -/
def catPullbackConeTetrahedron (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) (r : Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋3⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyTetrahedron (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeHomotopy p q) (ULift.up (nerve.edgeMk f).edge) r
/-- 概要：最初の三単体の上面は置換後の錐の元の三角形。
方針：同じ全錐のホモトピーの標準三角形への制限を使う。
規約：三単体の充填を新しく選択しない。
使われ方：二脚の比較と native な可換性の同時照合。 -/
lemma catPullbackConeTetrahedron_first (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 0 (catPullbackConeTetrahedron p q f 0) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.catPullbackReplacementCone p q) (ULift.up (nerve.edgeMk f).edge) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyTetrahedron_first _ _
/-- 概要：最後の三単体の下面は元の錐の指定三角形。
方針：同じ全錐のホモトピーの標準三角形への制限を使う。
規約：三単体の充填を新しく選択しない。
使われ方：二脚の比較と native な可換性の同時照合。 -/
lemma catPullbackConeTetrahedron_last (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 3 (catPullbackConeTetrahedron p q f 2) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeTriangle p q f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyTetrahedron_last _ _
/-- 概要：最初と中央の比較三単体の共有面が一致。
方針：同じ全錐のホモトピーの標準三角形への制限を使う。
規約：三単体の充填を新しく選択しない。
使われ方：二脚の比較と native な可換性の同時照合。 -/
lemma catPullbackConeTetrahedron_glue_first (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 1 (catPullbackConeTetrahedron p q f 0) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 1 (catPullbackConeTetrahedron p q f 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyTetrahedron_glue_first _ _
/-- 概要：中央と最後の比較三単体の共有面が一致。
方針：同じ全錐のホモトピーの標準三角形への制限を使う。
規約：三単体の充填を新しく選択しない。
使われ方：二脚の比較と native な可換性の同時照合。 -/
lemma catPullbackConeTetrahedron_glue_last (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 2 (catPullbackConeTetrahedron p q f 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.δ 2 (catPullbackConeTetrahedron p q f 2) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyTetrahedron_glue_last _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
