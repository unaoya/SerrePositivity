module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedTransportPrismFamily

/-!
概要：可変初期値を持つ元の全 pointed 延長を、同じ延長族の全空間の切断へ束ねる。
方針：元の持ち上げを curry し、相対内部 Hom の引き戻しへ持ち上げる。
規約：元の持ち上げを選び直さない。使われ方：第零面の実制限と全族の比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {A C E B K : SSet.{u + 1}} {i : C ⟶ A} {p : E ⟶ B}
  (D : PointedTransportPrismFamily (K := K) i p)
  (W : (A ⊗ E) ⊗ K ⟶ PointedSpaceInfinity.{u})
  (hb : ((i ▷ E) ▷ K) ≫ W = D.boundary)
  (hp : W ≫ pointedSpaceProjection = ((A ◁ p) ▷ K) ≫ D.diagram)

/-- 元の実延長をそのまま可変初期値の全延長空間へ束ねる切断。 -/
def pointedPrismFamilySection : K ⟶ D.liftSpace := by
  let r := pointedTransportPrismRelativeHom i E
  have hd₀ : D.data ≫ r.fst = curry D.boundary :=
    relativeBoundaryFamilyData_fst _ _ _ _ _ _
  have hd₁ : D.data ≫ r.snd = curry (((A ◁ p) ▷ K) ≫ D.diagram) :=
    relativeBoundaryFamilyData_snd _ _ _ _ _ _
  have hw : curry W ≫ r.π = 𝟙 K ≫ D.data := by
    apply r.hom_ext
    · rw [Category.assoc, r.π_fst, Category.id_comp, hd₀]
      change curry W ≫ (pre (i ▷ E)).app PointedSpaceInfinity = curry D.boundary
      apply uncurry_injective
      rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
      exact hb
    · rw [Category.assoc, r.π_snd, Category.id_comp, hd₁]
      change curry W ≫ (ihom (A ⊗ E)).map pointedSpaceProjection =
        curry (((A ◁ p) ▷ K) ≫ D.diagram)
      apply uncurry_injective
      rw [uncurry_natural_right, uncurry_curry, uncurry_curry]
      exact hp
  exact pullback.lift (curry W) (𝟙 K) hw

/-- 元の全延長による切断は、全パラメータを厳密に保持する。 -/
lemma pointedPrismFamilySection_projection :
    pointedPrismFamilySection D W hb hp ≫ D.liftSpaceProjection = 𝟙 K :=
  pullback.lift_snd _ _ _

/-- 切断の関手空間成分は、元の実延長の curry そのもの。 -/
lemma pointedPrismFamilySection_curry :
    pointedPrismFamilySection D W hb hp ≫
      relativeBoundaryFamilyCurry (pointedTransportPrismRelativeHom i E) D.data = curry W :=
  pullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories.F2
