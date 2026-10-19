module

public import SerrePositivity.InfinityCategories.F1.CylinderSquareComparisonLaws

/-!
概要：prism 中間模型と両端同値の実際の円柱上の四角形の厳密な同型。
方針：普遍 lift の射影とパラメーター付き pushout の一意性で両往復を示す。
規約：両端・底・全空間の全てを高次単体ごとに保持する。
使われ方：円柱上の実際の両端制限の trivial Kan fibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：円柱の中間模型への二射は普遍 lift と両端が一致すれば等しい。
方針：二つの引き戻しの一意性を使う。
規約：両端だけでなく全 prism の lift を比較する。
使われ方：中間模型への往復の恒等性。 -/
lemma pointedCylinderPrism_hom_ext {K J L : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌)
    {F G : L ⟶ pointedCylinderPrismSpace f s t}
    (hP : F ≫ pointedCylinderPrismLift f s t = G ≫ pointedCylinderPrismLift f s t)
    (hE : F ≫ pointedCylinderPrismEndpoints f s t = G ≫ pointedCylinderPrismEndpoints f s t) :
    F = G := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact hP
    · change F ≫ pullback.fst _ _ ≫ pointedPrismEquivalenceEndpoints K s t =
        G ≫ pullback.fst _ _ ≫ pointedPrismEquivalenceEndpoints K s t
      rw [pullback.condition]
      exact congrArg (fun w ↦ w ≫ pointedCylinderPrismEndpointData f s t) hE
  · exact hE

/-- 概要：円柱の prism 模型から実際の両端同値の四角形へ移す厳密な同型。
方針：構成済みの順比較と逆比較の両往復を普遍性で確認する。
規約：同値や同型の存在だけでなく実際の二射を指定する。
使われ方：実際の四角形の両端制限へ中間模型の充填性を移す。 -/
def pointedCylinderEquivalenceSquareIso {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderPrismSpace f s t ≅ cylinderEquivalenceSquareSpace f s t where
  hom := pointedCylinderEquivalenceSquareMap f s t
  inv := cylinderEquivalenceSquareInverse f s t
  hom_inv_id := by
    apply pointedCylinderPrism_hom_ext f s t
    · rw [Category.assoc, cylinderEquivalenceSquareInverse_lift, ← Category.assoc,
        pointedCylinderEquivalenceSquareMap_forget, pointedCylinderFixedSquareMap_lift,
        Category.id_comp]
    · rw [Category.assoc, cylinderEquivalenceSquareInverse_endpoints,
        pointedCylinderEquivalenceSquareMap_endpoints, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · change _ ≫ cylinderEquivalenceSquareForget f s t = _
      rw [Category.assoc, pointedCylinderEquivalenceSquareMap_forget,
        cylinderEquivalenceSquareInverse_fixedSquare, Category.id_comp]
      rfl
    · change _ ≫ cylinderEquivalenceSquareEndpoints f s t = _
      rw [Category.assoc, pointedCylinderEquivalenceSquareMap_endpoints,
        cylinderEquivalenceSquareInverse_endpoints, Category.id_comp]
      rfl

/-- 概要：同型は両端の同値の族を厳密に保つ。
方針：順比較の両端射影の公式。
規約：同型の底の射は恒等。
使われ方：両端制限の充填性の移送。 -/
lemma pointedCylinderEquivalenceSquareIso_endpoints {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    (pointedCylinderEquivalenceSquareIso f s t).hom ≫ cylinderEquivalenceSquareEndpoints f s t =
      pointedCylinderPrismEndpoints f s t := pointedCylinderEquivalenceSquareMap_endpoints f s t

/-- 概要：実際の円柱上の両端同値の四角形の両端制限は trivial Kan fibration。
方針：中間模型の全境界充填を厳密な同型で移す。
規約：終点の貼り付け射 f に同値性は要求しない。
使われ方：Kerodon Lemma 5.6.9.1 の円柱側の境界固定延長。 -/
lemma cylinderEquivalenceSquareEndpoints_trivialKanFibration {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : SpaceInfinity.{u} _⦋0⦌) :
    TrivialKanFibration (cylinderEquivalenceSquareEndpoints f s t) := by
  have h := pointedCylinderPrismEndpoints_trivialKanFibration f s t
  rw [← cylinderEquivalenceSquareInverse_endpoints f s t]
  exact ⟨trivialKanFibrations.comp_mem _ _
    (MorphismProperty.rlp_of_isIso _ (pointedCylinderEquivalenceSquareIso f s t).inv) h.mem⟩

end SerrePositivity.InfinityCategories
