module
public import Mathlib.CategoryTheory.Groupoid.Basic
public import Mathlib.CategoryTheory.Endomorphism

/-! # 亜群の辺路を同じ基点の群で比較する
概要：基点の連結成分の射を基点の自己同型へ移し、平行射の等号を検出する。
方針：基点から各対象への道を一度選び、両端で共役する。他成分には単位元を割り当てる。
規約：道の選択は計算補助であり、平行射の検出は忠実性から証明する。
使われ方：全三角形・境界固定円柱の関係を一つの群で計算し、元の平行辺へ戻す。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
variable {C : Type u} [Groupoid.{v} C] (c : C)

/-- 基点から到達可能な対象への固定された道。 -/
def groupoidBasedPath (x : C) (hx : Nonempty (c ⟶ x)) : c ⟶ x := hx.some

/-- 到達可能な両端を持つ射を、同じ基点の自己同型へ移す。 -/
def groupoidBasedArrowAt {x y : C} (f : x ⟶ y)
    (hx : Nonempty (c ⟶ x)) (hy : Nonempty (c ⟶ y)) : End c :=
  End.of (groupoidBasedPath c x hx ≫ f ≫ inv (groupoidBasedPath c y hy))

/-- 基点の成分の射は共役で移し、他成分の射には単位を割り当てる。 -/
def groupoidBasedArrow {x y : C} (f : x ⟶ y) : End c := by
  classical
  exact if hx : Nonempty (c ⟶ x) then
    groupoidBasedArrowAt c f hx ⟨hx.some ≫ f⟩ else 1

/-- 到達可能な両端では、固定した両端の道による元の表示を回収する。 -/
lemma groupoidBasedArrow_eq {x y : C} (f : x ⟶ y)
    (hx : Nonempty (c ⟶ x)) (hy : Nonempty (c ⟶ y)) :
    groupoidBasedArrow c f = groupoidBasedArrowAt c f hx hy := by
  simp only [groupoidBasedArrow, dite_eq_left hx]

/-- 同じ端点の二射は、同じ基点へ移した値によって検出できる。 -/
lemma groupoidBasedArrow_injective {x y : C} (hx : Nonempty (c ⟶ x))
    (f g : x ⟶ y) (h : groupoidBasedArrow c f = groupoidBasedArrow c g) : f = g := by
  have hy : Nonempty (c ⟶ y) := ⟨hx.some ≫ f⟩
  rw [groupoidBasedArrow_eq c f hx hy, groupoidBasedArrow_eq c g hx hy] at h
  have he := congrArg End.asHom h
  change groupoidBasedPath c x hx ≫ f ≫ inv (groupoidBasedPath c y hy) =
    groupoidBasedPath c x hx ≫ g ≫ inv (groupoidBasedPath c y hy) at he
  exact (cancel_mono (inv (groupoidBasedPath c y hy))).mp
    ((cancel_epi (groupoidBasedPath c x hx)).mp he)

/-- 合成は同じ基点の自己同型群の積へ移る。 -/
lemma groupoidBasedArrow_comp {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    groupoidBasedArrow c (f ≫ g) = groupoidBasedArrow c g * groupoidBasedArrow c f := by
  classical
  by_cases hx : Nonempty (c ⟶ x)
  · have hy : Nonempty (c ⟶ y) := ⟨hx.some ≫ f⟩
    have hz : Nonempty (c ⟶ z) := ⟨hy.some ≫ g⟩
    rw [groupoidBasedArrow_eq c (f ≫ g) hx hz, groupoidBasedArrow_eq c f hx hy,
      groupoidBasedArrow_eq c g hy hz]
    apply End.ext
    simp only [groupoidBasedArrowAt, End.mul_asHom,
      Category.assoc, IsIso.inv_hom_id_assoc]
  · have hy : ¬ Nonempty (c ⟶ y) := by
      rintro ⟨q⟩
      exact hx ⟨q ≫ inv f⟩
    simp only [groupoidBasedArrow, dite_eq_right hx, dite_eq_right hy, one_mul]

/-- 恒等射は、どの成分でも群の単位へ移る。 -/
lemma groupoidBasedArrow_id (x : C) : groupoidBasedArrow c (𝟙 x) = 1 := by
  classical
  by_cases hx : Nonempty (c ⟶ x)
  · rw [groupoidBasedArrow_eq c (𝟙 x) hx hx]
    apply End.ext
    simp only [groupoidBasedArrowAt, End.one_asHom, Category.id_comp,
      IsIso.hom_inv_id]
  · simp only [groupoidBasedArrow, dite_eq_right hx]

end SerrePositivity.KST.SConstruction
