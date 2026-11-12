module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofRelativeTransportTriangle

/-! # 相対輸送三角形から第二辺を取り出す

概要：境界固定比較の終端から元の指定目標へ、同じ底辺上の実輸送を取り出す。
方針：充填三角形の辺十二と零退化の全辺の公式を使う。
規約：元の指定輸送と境界上で厳密に一致。使われ方：実屋根の有限相対充填の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
variable {K L E B : SSet.{u}} {p : E ⟶ B} {j : K ⟶ L}
variable {f₀ f₁ g : L ⟶ E} {C : SSet.Homotopy f₀ f₁} {T : SSet.Homotopy f₀ g}
variable (D : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofRelativeTransportTriangle p j C T)

/-- 相対三角形の第二辺は、比較後の実充填から元の指定目標への輸送。 -/
def RoofRelativeTransportTriangle.homotopy : SSet.Homotopy f₁ g where
  h := (L ◁ (SSet.stdSimplex.δ (0 : Fin 3))) ≫ D.family
  h₀ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstTriangle_edge12_source, Category.assoc, D.first]
    exact C.h₁
  h₁ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstTriangle_edge12_target, Category.assoc, D.diagonal]
    exact T.h₁
  rel := by
    ext n s
    exact False.elim s.1.2

/-- 得た実輸送の境界は、指定された元の輸送と全時刻で厳密に一致。 -/
lemma RoofRelativeTransportTriangle.homotopy_boundary :
    (j ▷ Δ[1]) ≫ D.homotopy.h = (j ▷ Δ[1]) ≫ T.h := by
  change (j ▷ Δ[1]) ≫ ((L ◁ (SSet.stdSimplex.δ (0 : Fin 3))) ≫ D.family) = _
  rw [← whisker_exchange_assoc, D.boundary, ← Category.assoc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstTriangleCollapse_edge12, whiskerLeft_id, Category.id_comp]

/-- 得た実輸送は、元の指定輸送と同じ底の族を厳密に被覆する。 -/
lemma RoofRelativeTransportTriangle.homotopy_over :
    D.homotopy.h ≫ p = T.h ≫ p := by
  change ((L ◁ (SSet.stdSimplex.δ (0 : Fin 3))) ≫ D.family) ≫ p = _
  rw [Category.assoc, D.over, ← Category.assoc, ← whiskerLeft_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFirstTriangleCollapse_edge12, whiskerLeft_id, Category.id_comp]

/-- 全時間の射影が一点なら、射影は始端を全時間に延長した族そのもの。 -/
lemma roofHomotopy_over_constant {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) {Z : SSet.{u}} (q : Y ⟶ Z) (z : Z _⦋0⦌)
    (hq : H.h ≫ q = SSet.const z) :
    H.h ≫ q = CartesianMonoidalCategory.fst X Δ[1] ≫ f ≫ q := by
  have hf : f ≫ q = SSet.const z := by
    rw [← H.h₀, Category.assoc, hq, SSet.comp_const]
  rw [hf, SSet.comp_const]
  exact hq

end SerrePositivity.InfinityCategories.Project.DerivedCategories
