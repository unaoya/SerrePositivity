module

public import SerrePositivity.InfinityCategories.F1B.KanExtensionShapes
public import SerrePositivity.InfinityCategories.Core.SliceMap

/-!
概要：comma 上の全パラメータ族を、元の指定頂点への全余錐から構成する。
方針：slice の curry と厳密な引き戻しの普遍性を使う。
規約：全図式・全余錐を保持。使われ方：有限図式の filtered 表示の境界延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ始域図式と指定頂点への全余錐が定める comma の全パラメータ族。 -/
def commaFamilyLift {A B X : SSet.{u}} (δ : B ⟶ X) (x : X _⦋0⦌)
    (a : A ⟶ B) (F : join A (Δ[0] : SSet.{u}) ⟶ X)
    (hl : joinInl A Δ[0] ≫ F = a ≫ δ)
    (hr : joinInr A Δ[0] ≫ F = SSet.yonedaEquiv.symm x) : A ⟶ leftKanShape δ x :=
  pullback.lift a (sliceOverCurry F hr) (by rw [sliceOverCurry_projection]; exact hl.symm)

/-- 元の始域図式は厳密に回収される。 -/
lemma commaFamilyLift_projection {A B X : SSet.{u}} (δ : B ⟶ X) (x : X _⦋0⦌)
    (a : A ⟶ B) (F : join A (Δ[0] : SSet.{u}) ⟶ X) (hl) (hr) :
    commaFamilyLift δ x a F hl hr ≫ leftKanProjection δ x = a :=
  pullback.lift_fst _ _ _

/-- 同じ族から読み戻した全余錐の射は、元の全射そのもの。 -/
lemma commaFamilyLift_uncurry {A B X : SSet.{u}} (δ : B ⟶ X) (x : X _⦋0⦌)
    (a : A ⟶ B) (F : join A (Δ[0] : SSet.{u}) ⟶ X) (hl) (hr) :
    sliceOverUncurry (commaFamilyLift δ x a F hl hr ≫
      pullback.snd δ (sliceOverProjection (SSet.yonedaEquiv.symm x))) = F := by
  rw [commaFamilyLift, pullback.lift_snd, sliceOverUncurry_curry]

/-- 元の任意の全 comma 族は、その始域図式と全余錐から厳密に再構成される。 -/
lemma commaFamilyLift_eta {A B X : SSet.{u}} (δ : B ⟶ X) (x : X _⦋0⦌)
    (q : A ⟶ leftKanShape δ x) :
    commaFamilyLift δ x (q ≫ leftKanProjection δ x)
      (sliceOverUncurry (q ≫ pullback.snd δ
        (sliceOverProjection (SSet.yonedaEquiv.symm x))))
      (by rw [sliceOverUncurry_projection, Category.assoc, ← pullback.condition,
        ← Category.assoc]) (sliceOverUncurry_fixed _) = q := by
  apply pullback.hom_ext
  · exact commaFamilyLift_projection _ _ _ _ _ _
  · rw [commaFamilyLift, pullback.lift_snd, sliceOverCurry_uncurry]

/-- 全族の持ち上げは任意のパラメータの制限と厳密に可換。 -/
lemma commaFamilyLift_precomp {A₀ A B X : SSet.{u}} (δ : B ⟶ X) (x : X _⦋0⦌)
    (a : A ⟶ B) (F : join A (Δ[0] : SSet.{u}) ⟶ X) (hl) (hr) (g : A₀ ⟶ A) :
    g ≫ commaFamilyLift δ x a F hl hr =
    commaFamilyLift δ x (g ≫ a) (joinMap g (𝟙 Δ[0]) ≫ F)
      (by rw [← Category.assoc, joinInl_joinMap, Category.assoc, hl, ← Category.assoc])
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp]; exact hr) := by
  apply pullback.hom_ext
  · rw [Category.assoc, commaFamilyLift_projection, commaFamilyLift_projection]
  · simp only [commaFamilyLift, Category.assoc, pullback.lift_snd]
    exact sliceOverCurry_precomp F hr g

end SerrePositivity.InfinityCategories.F2.Ind
