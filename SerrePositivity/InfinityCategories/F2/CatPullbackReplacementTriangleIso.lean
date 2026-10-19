module

public import SerrePositivity.InfinityCategories.F2.StrictNativeConeTriangle
public import SerrePositivity.InfinityCategories.F2.CatPullbackReplacementCone
public import SerrePositivity.InfinityCategories.F2.CatTriangleFacesEquality

/-!
概要：置換後の strict な錐の指定三角形の同型。
方針：全錐の同じ指定比較円柱とその面の同定を使う。
規約：共有面の同型を選び直さず元の単体から読む。
使われ方：二射影の指定比較同型と指定 path の整合の証明。
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
/-- 概要：通常の錐の三辺を保つ置換後の指定三角形の同型。
方針：元の三角形の同型と境界関手を揃えて四面の合成則を使う。
規約：指定同型の存在でなく元の値と合成の等式を保持する。
使われ方：三つの比較三単体の関係から二脚の比較の整合を導く。 -/
def catPullbackReplacementTriangleIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    FunctorIso ((catPullbackReplacementOrdinaryCone p q).π.app j)
      ((catPullbackReplacementOrdinaryCone p q).π.app i ≫
        (catPullbackReplacementDiagram p q).map f) :=
  catInfinityTriangleIso_of_faces _ _ _
    (nativeConeTriangle (catPullbackReplacementCone p q) (ULift.up (nerve.edgeMk f).edge))
    (nativeConeTriangle_strict_two (catPullbackReplacementOrdinaryCone p q) f)
    (nativeConeTriangle_strict_zero (catPullbackReplacementOrdinaryCone p q) f)
    (nativeConeTriangle_strict_one (catPullbackReplacementOrdinaryCone p q) f)
/-- 概要：指定三角形の同型は元の二単体の同型と型を含めて等しい。
方針：元の三角形の同型と境界関手を揃えて四面の合成則を使う。
規約：指定同型の存在でなく元の値と合成の等式を保持する。
使われ方：三つの比較三単体の関係から二脚の比較の整合を導く。 -/
lemma catPullbackReplacementTriangleIso_heq (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    HEq (catPullbackReplacementTriangleIso p q f)
      (catInfinityTriangleIso
        (nativeConeTriangle (catPullbackReplacementCone p q) (ULift.up (nerve.edgeMk f).edge))) :=
  catInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
