module

public import SerrePositivity.AlgebraicGeometry.BaseChangedModelTriple

/-!
概要：任意の構造射を保つ三重交叉の同型は、二射影の底変換射と可換。
方針：段の基底座標と固定模型への二射影を照合する。
規約：構造射の可換式を保持し、係数射に追加仮定を置かない。
使われ方：G2 の後段での三重交叉の gluing の式。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {B S U V W : Scheme.{u}}
  (γ : B ⟶ S) (p : U ⟶ S) (q : V ⟶ S) (r : W ⟶ S)
  (a : V ⟶ U) (c : W ⟶ U) (ha : a ≫ p = q) (hc : c ≫ p = r)

/-- 一般形の三重交叉の同型は、第一射影の実際の底変換と可換。 -/
@[reassoc (attr := simp)] theorem baseChangedModelTripleIso_hom_fstArrow :
    (baseChangedModelTripleIso γ p q r a c ha hc).hom ≫
      baseChangedModelArrow γ (pullback.fst a c ≫ a ≫ p) q (pullback.fst a c)
        (by rw [← ha]) =
      pullback.fst (baseChangedModelArrow γ q p a ha) (baseChangedModelArrow γ r p c hc) := by
  apply pullback.hom_ext <;>
    simp [Category.assoc, baseChangedModelTripleComparison, cartesianPullbackMap]

/-- 一般形の三重交叉の同型は、第二射影の実際の底変換と可換。 -/
@[reassoc (attr := simp)] theorem baseChangedModelTripleIso_hom_sndArrow :
    (baseChangedModelTripleIso γ p q r a c ha hc).hom ≫
      baseChangedModelArrow γ (pullback.fst a c ≫ a ≫ p) r (pullback.snd a c)
        (by rw [← hc]; simpa only [Category.assoc] using
          congrArg (fun z ↦ z ≫ p) (pullback.condition (f := a) (g := c)).symm) =
      pullback.snd (baseChangedModelArrow γ q p a ha) (baseChangedModelArrow γ r p c hc) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangedModelArrow_fst, baseChangedModelTripleIso_hom_fst]
    have he := congrArg (fun z ↦ z ≫ pullback.fst γ p)
      (pullback.condition (f := baseChangedModelArrow γ q p a ha)
        (g := baseChangedModelArrow γ r p c hc))
    simpa only [Category.assoc, baseChangedModelArrow_fst] using he
  · simp [Category.assoc, baseChangedModelTripleComparison, cartesianPullbackMap]

end SerrePositivity.AlgebraicGeometry
