module

public import SerrePositivity.KST.Spectra.PointedVertexComparison
public import SerrePositivity.KST.Spectra.PointedExchangeVertices

/-!
概要：点つき閉構造の単位で表す写像族と、基礎単体集合の単位で表す同じ族の一致。
方針：非基点側の単位の右単位子を、smash 商と基点付き Hom の包含で計算する。
規約：Kan 性は不要。使われ方：cotensor の恒等射の像の BK 切断を元の普遍評価へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 点つき curry' の非基点側を Hom の包含に続けると、基礎の curry' そのもの。 -/
@[reassoc]
lemma unitUnderlyingHom_curry'_ι {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    PointedSimplicialSet.unitUnderlyingHom (PointedObject.basedHom X Y) (curry' f) ≫
        PointedObject.basedHomι X Y = curry' f.right := by
  dsimp only [PointedSimplicialSet.unitUnderlyingHom, PointedObject.adjoinHomEquiv,
    Equiv.coe_fn_mk, MonoidalClosed.curry']
  rw [curry_eq_smashCurry, Category.assoc, PointedObject.smashCurry_ι,
    ← curry_natural_left]
  congr 1
  simp only [Under.comp_right]
  erw [nonbasepoint_right_unit_assoc]

end SerrePositivity.KST.Spectra.PointedMapping
