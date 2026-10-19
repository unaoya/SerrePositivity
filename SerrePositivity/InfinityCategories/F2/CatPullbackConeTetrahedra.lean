module

public import SerrePositivity.InfinityCategories.F2.ConeHomotopyTetrahedra
public import SerrePositivity.InfinityCategories.F2.CatPullbackConeTriangle
public import SerrePositivity.InfinityCategories.F2.CatPullbackConeHomotopy

/-!
概要：引き戻し錐の比較円柱の実際の三単体と上下・共有面。
方針：元の指定ホモトピーを各 cospan の射上の三角形に制限する。
規約：元と置換後の錐の三角形を厳密に回収する。
使われ方：四面の関手同型の合成則の引き戻し錐への適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：引き戻し錐の指定比較円柱を構成する三つの三単体。
方針：同じ全錐のホモトピーの標準三角形への制限を使う。
規約：三単体の充填を新しく選択しない。
使われ方：二脚の比較と native な可換性の同時照合。 -/
def catPullbackConeTetrahedron (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) (r : Fin 3) : CatInfinity.{u} _⦋3⦌ :=
  coneHomotopyTetrahedron (catPullbackConeHomotopy p q) (ULift.up (nerve.edgeMk f).edge) r
/-- 概要：最初の三単体の上面は置換後の錐の元の三角形。
方針：同じ全錐のホモトピーの標準三角形への制限を使う。
規約：三単体の充填を新しく選択しない。
使われ方：二脚の比較と native な可換性の同時照合。 -/
lemma catPullbackConeTetrahedron_first (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 0 (catPullbackConeTetrahedron p q f 0) =
      nativeConeTriangle (catPullbackReplacementCone p q) (ULift.up (nerve.edgeMk f).edge) :=
  coneHomotopyTetrahedron_first _ _
/-- 概要：最後の三単体の下面は元の錐の指定三角形。
方針：同じ全錐のホモトピーの標準三角形への制限を使う。
規約：三単体の充填を新しく選択しない。
使われ方：二脚の比較と native な可換性の同時照合。 -/
lemma catPullbackConeTetrahedron_last (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 3 (catPullbackConeTetrahedron p q f 2) = catPullbackConeTriangle p q f :=
  coneHomotopyTetrahedron_last _ _
/-- 概要：最初と中央の比較三単体の共有面が一致。
方針：同じ全錐のホモトピーの標準三角形への制限を使う。
規約：三単体の充填を新しく選択しない。
使われ方：二脚の比較と native な可換性の同時照合。 -/
lemma catPullbackConeTetrahedron_glue_first (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 1 (catPullbackConeTetrahedron p q f 0) =
      CatInfinity.δ 1 (catPullbackConeTetrahedron p q f 1) :=
  coneHomotopyTetrahedron_glue_first _ _
/-- 概要：中央と最後の比較三単体の共有面が一致。
方針：同じ全錐のホモトピーの標準三角形への制限を使う。
規約：三単体の充填を新しく選択しない。
使われ方：二脚の比較と native な可換性の同時照合。 -/
lemma catPullbackConeTetrahedron_glue_last (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 2 (catPullbackConeTetrahedron p q f 1) =
      CatInfinity.δ 2 (catPullbackConeTetrahedron p q f 2) :=
  coneHomotopyTetrahedron_glue_last _ _

end SerrePositivity.InfinityCategories.F2
