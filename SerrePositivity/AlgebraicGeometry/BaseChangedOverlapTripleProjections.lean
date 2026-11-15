module

public import SerrePositivity.AlgebraicGeometry.BaseChangedModelArrow
public import SerrePositivity.AlgebraicGeometry.BaseChangedOverlapTriple

/-!
概要：三重交叉の具体的な底変換同型は、二射影の実際の底変換射と可換。
方針：基底座標と固定模型への射影の二射影で判定する。
規約：重なりの射・基底射は任意で、平坦性・単射性を仮定しない。
使われ方：G2 の有限段へ移した式を実際の三重交叉の gluing の式へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {B S U V W : Scheme.{u}}
  (γ : B ⟶ S) (p : U ⟶ S) (q : V ⟶ U) (r : W ⟶ U)

/-- 三重交叉の同型は、第一射影の実際の底変換と可換。 -/
@[reassoc (attr := simp)] theorem baseChangedOverlapTripleIso_hom_fstArrow :
    (baseChangedOverlapTripleIso γ p q r).hom ≫
      baseChangedModelArrow γ (pullback.fst q r ≫ q ≫ p) (q ≫ p) (pullback.fst q r) rfl =
      pullback.fst (baseChangedOverlapMap γ p q) (baseChangedOverlapMap γ p r) := by
  apply pullback.hom_ext <;>
    simp [Category.assoc, baseChangedOverlapTripleComparison, cartesianPullbackMap]

/-- 三重交叉の同型は、第二射影の実際の底変換とも可換。 -/
@[reassoc (attr := simp)] theorem baseChangedOverlapTripleIso_hom_sndArrow :
    (baseChangedOverlapTripleIso γ p q r).hom ≫
      baseChangedModelArrow γ (pullback.fst q r ≫ q ≫ p) (r ≫ p) (pullback.snd q r)
        (by simpa only [Category.assoc] using
          congrArg (fun z ↦ z ≫ p) (pullback.condition (f := q) (g := r)).symm) =
      pullback.snd (baseChangedOverlapMap γ p q) (baseChangedOverlapMap γ p r) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangedModelArrow_fst, baseChangedOverlapTripleIso_hom_fst]
    rw [pullback.condition_assoc]
    simp
  · simp [Category.assoc, baseChangedOverlapTripleComparison, cartesianPullbackMap]

end SerrePositivity.AlgebraicGeometry
