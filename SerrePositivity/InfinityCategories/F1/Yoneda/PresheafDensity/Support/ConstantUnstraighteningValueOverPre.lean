module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantUnstraighteningRelativeProjection
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverPrecomposition

/-!
概要：定値相対 Hom の値への作用は、元の底上の射による前合成と厳密に可換する。
方針：全係数の射影表示と内部 Hom の前合成の自然性を使う。
規約：元の射と係数を保持。使われ方：三角形の最後の辺の同じ全空間上への制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の定値標的の値への比較は、同じ底上の射による前合成と全族で可換する。 -/
lemma constantUnstraighteningRelativeIso_value_overPre {A C B : SSet.{u + 1}}
    (p : A ⟶ B) (d : C ⟶ B) (t : C ⟶ A) (ht : t ≫ p = d)
    (z : SpaceInfinity.{u} _⦋0⦌) :
    relativeFunctorOverPre (leftUnstraighteningProjection (SSet.const z : B ⟶ SpaceInfinity))
        (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht) ≫
      ((constantUnstraighteningRelativeIso d z).hom ≫
        (ihom C).map (pointedSpaceFiberValueEquivalence z).hom) =
      ((constantUnstraighteningRelativeIso p z).hom ≫
        (ihom A).map (pointedSpaceFiberValueEquivalence z).hom) ≫
          (pre t).app ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj) := by
  simp only [constantUnstraighteningRelativeIso_value_eq_projection, Category.assoc]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F2
