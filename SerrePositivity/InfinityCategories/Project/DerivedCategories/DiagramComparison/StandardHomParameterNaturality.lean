module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardTopBoundary

/-!
概要：実標準Homへの全パラメータ射の自然性を元の引き戻しで評価する。
方針：同じ自然変換の成分自然性を一つの単体に適用する。
規約：全単体作用素と元の標準Homの引き戻しを保持する既存構成の法則。
使われ方：HA 1.2.4、IS-W2 B02のAW前面・後面のパラメータ成分。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 実標準Homへの元の射の低い単体での値は、同じ高い単体の標準引き戻し。 -/
theorem standardHomParameter_map {S : SSet.{u}}
    (f : S ⟶ standardHomSpace (R := A) x y) {m n : SimplexCategory}
    (θ : m ⟶ n) (s : S.obj (Opposite.op n)) :
    f.app (Opposite.op m) (S.map θ.op s) =
      standardPullback θ.toOrderHom (f.app (Opposite.op n) s) := by
  have h := ConcreteCategory.congr_hom (f.naturality θ.op) s
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
