module

public import SerrePositivity.InfinityCategories.F1B.UnitLeftZigzagPointwise
public import SerrePositivity.InfinityCategories.F1B.TriangleIdempotence

/-!
概要：各点の標準単位比較条件から構成した余単位の左三角恒等式を証明する。
方針：右三角恒等式による冪等性と、各点の一意性による左 zigzag の可逆性を合わせる。
規約：各点での恒等性を全体の恒等性とは扱わない。
使われ方：B1 の指定単位から随伴データへの接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories
local instance leftTriangleHomCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

/-- 概要：双圏の左 zigzag の表示は h Fun の前後合成の式。
方針：結合子を明示して厳密性で消し、左右 whisker の表示を使う。
規約：単位・余単位の任意の候補について成立する。
使われ方：双圏の冪等性を h Fun へ移す。 -/
lemma qcatLeftZigzag_hom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (ε : FunctorHom (G ≫ F) (𝟙 Y)) :
    (qcatHomFunctor X Y).map (leftZigzag
      ((qcatCellEquiv (𝟙 X) (F ≫ G)).symm η)
      ((qcatCellEquiv (G ≫ F) (𝟙 Y)).symm ε)) = unitLeftZigzag η ε := by
  let η' : 𝟙 (qcatOf X) ⟶ qcatMap F ≫ qcatMap G := (qcatCellEquiv (𝟙 X) (F ≫ G)).symm η
  let ε' : qcatMap G ≫ qcatMap F ⟶ 𝟙 (qcatOf Y) := (qcatCellEquiv (G ≫ F) (𝟙 Y)).symm ε
  have hn := bicategory_leftZigzag_explicit (B := SSet.QCat.{u})
    (f := qcatMap F) (g := qcatMap G) η' ε'
  erw [hn]
  simp only [Strict.associator_eqToIso, eqToIso.hom, eqToHom_refl, Category.id_comp]
  change qcatCellEquiv _ _ (η' ▷ qcatMap F) ≫ qcatCellEquiv _ _ (qcatMap F ◁ ε') = _
  exact congrArg₂ (· ≫ ·) (qcatCell_whiskerRight η' F) (qcatCell_whiskerLeft F ε')

/-- 概要：双圏の右 zigzag の表示は h Fun の前後合成の式。
方針：結合子を明示して厳密性で消し、左右 whisker の表示を使う。
規約：単位・余単位の任意の候補について成立する。
使われ方：構成した余単位の右三角恒等式を双圏へ戻す。 -/
lemma qcatRightZigzag_hom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (ε : FunctorHom (G ≫ F) (𝟙 Y)) :
    (qcatHomFunctor Y X).map (rightZigzag
      ((qcatCellEquiv (𝟙 X) (F ≫ G)).symm η)
      ((qcatCellEquiv (G ≫ F) (𝟙 Y)).symm ε)) =
      (hoFunctor.map ((pre G).app X)).toFunctor.map η ≫
        (hoFunctor.map ((ihom Y).map G)).toFunctor.map ε := by
  let η' : 𝟙 (qcatOf X) ⟶ qcatMap F ≫ qcatMap G := (qcatCellEquiv (𝟙 X) (F ≫ G)).symm η
  let ε' : qcatMap G ≫ qcatMap F ⟶ 𝟙 (qcatOf Y) := (qcatCellEquiv (G ≫ F) (𝟙 Y)).symm ε
  have hn := bicategory_rightZigzag_explicit (B := SSet.QCat.{u})
    (f := qcatMap F) (g := qcatMap G) η' ε'
  erw [hn]
  simp only [Strict.associator_eqToIso, eqToIso.inv, eqToHom_refl, Category.id_comp]
  change qcatCellEquiv _ _ (qcatMap G ◁ η') ≫ qcatCellEquiv _ _ (ε' ▷ qcatMap G) = _
  exact congrArg₂ (· ≫ ·) (qcatCell_whiskerLeft G η') (qcatCell_whiskerRight ε' G)

/-- 概要：右三角恒等式があれば h Fun の左 zigzag は冪等。
方針：右三角恒等式を双圏へ戻し、一般の冪等性を表示関手で写す。
規約：左 zigzag の可逆性は不要。
使われ方：点ごとの単位条件から左三角恒等式へ進む。 -/
lemma unitLeftZigzag_idempotent {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (ε : FunctorHom (G ≫ F) (𝟙 Y))
    (hR : (hoFunctor.map ((pre G).app X)).toFunctor.map η ≫
      (hoFunctor.map ((ihom Y).map G)).toFunctor.map ε =
        𝟙 (HomotopyCategory.mk (functorVertex G))) :
    unitLeftZigzag η ε ≫ unitLeftZigzag η ε = unitLeftZigzag η ε := by
  let η' : 𝟙 (qcatOf X) ⟶ qcatMap F ≫ qcatMap G := (qcatCellEquiv (𝟙 X) (F ≫ G)).symm η
  let ε' : qcatMap G ≫ qcatMap F ⟶ 𝟙 (qcatOf Y) := (qcatCellEquiv (G ≫ F) (𝟙 Y)).symm ε
  have hr : rightZigzag η' ε' = (ρ_ (qcatMap G)).hom ≫ (λ_ (qcatMap G)).inv := by
    apply (qcatHomFunctor Y X).map_injective
    rw [qcatRightZigzag_hom]
    simp only [Strict.rightUnitor_eqToIso, Strict.leftUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp]
    exact hR
  have h := bicategory_leftZigzag_idempotent_of_right_triangle (B := SSet.QCat.{u})
    (f := qcatMap F) (g := qcatMap G) η' ε' hr
  have hn : leftZigzag η' ε' ⊗≫ leftZigzag η' ε' =
      leftZigzag η' ε' ≫ leftZigzag η' ε' := by
    dsimp [bicategoricalComp]
    simp only [Strict.rightUnitor_eqToIso, Strict.leftUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp]
  rw [hn] at h
  have hh := congrArg (qcatHomFunctor X Y).map h
  rw [CategoryTheory.Functor.map_comp] at hh
  have hl : (qcatHomFunctor X Y).map (leftZigzag η' ε') =
      unitLeftZigzag η ε := qcatLeftZigzag_hom η ε
  exact (congrArg₂ (· ≫ ·) hl hl).symm.trans (hh.trans hl)

/-- 概要：構成した余単位の左 zigzag は恒等射。
方針：右三角恒等式による冪等性から、点ごとの一意性で得た可逆な左因子を消去する。
規約：結論は h Fun 全体の等式。
使われ方：指定単位を持つ随伴の左三角恒等式。 -/
lemma UnitMappingSpaceCondition.left_triangle
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : FunctorHom (𝟙 X) (F ≫ G)}
    (hη : UnitMappingSpaceCondition η) (c : UnitCommaCounitData η) :
    unitLeftZigzag η c.counitHom = 𝟙 (HomotopyCategory.mk (functorVertex F)) := by
  have := hη.leftZigzag_isIso c
  apply (cancel_epi (unitLeftZigzag η c.counitHom)).1
  rw [unitLeftZigzag_idempotent η c.counitHom c.right_triangle, Category.comp_id]

end SerrePositivity.InfinityCategories
