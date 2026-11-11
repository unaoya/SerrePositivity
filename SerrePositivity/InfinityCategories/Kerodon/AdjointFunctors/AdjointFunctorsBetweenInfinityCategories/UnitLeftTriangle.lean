module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitLeftZigzagPointwise
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.TriangleIdempotence

/-!
概要：各点の標準単位比較条件から構成した余単位の左三角恒等式を証明する。
方針：右三角恒等式による冪等性と、各点の一意性による左 zigzag の可逆性を合わせる。
規約：各点での恒等性を全体の恒等性とは扱わない。
使われ方：B1 の指定単位から随伴データへの接続。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
local instance leftTriangleHomCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

/-- 概要：双圏の左 zigzag の表示は h Fun の前後合成の式。
方針：結合子を明示して厳密性で消し、左右 whisker の表示を使う。
規約：単位・余単位の任意の候補について成立する。
使われ方：双圏の冪等性を h Fun へ移す。 -/
lemma qcatLeftZigzag_hom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (ε : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (G ≫ F) (𝟙 Y)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X Y).map (leftZigzag
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (F ≫ G)).symm η)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (G ≫ F) (𝟙 Y)).symm ε)) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag η ε := by
  let η' : 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf X) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (F ≫ G)).symm η
  let ε' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ⟶ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf Y) := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (G ≫ F) (𝟙 Y)).symm ε
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_leftZigzag_explicit (B := SSet.QCat.{u})
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G) η' ε'
  erw [hn]
  simp only [Strict.associator_eqToIso, eqToIso.hom, eqToHom_refl, Category.id_comp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (η' ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ◁ ε') = _
  exact congrArg₂ (· ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight η' F) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft F ε')

/-- 概要：双圏の右 zigzag の表示は h Fun の前後合成の式。
方針：結合子を明示して厳密性で消し、左右 whisker の表示を使う。
規約：単位・余単位の任意の候補について成立する。
使われ方：構成した余単位の右三角恒等式を双圏へ戻す。 -/
lemma qcatRightZigzag_hom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (ε : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (G ≫ F) (𝟙 Y)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor Y X).map (rightZigzag
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (F ≫ G)).symm η)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (G ≫ F) (𝟙 Y)).symm ε)) =
      (hoFunctor.map ((pre G).app X)).toFunctor.map η ≫
        (hoFunctor.map ((ihom Y).map G)).toFunctor.map ε := by
  let η' : 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf X) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (F ≫ G)).symm η
  let ε' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ⟶ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf Y) := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (G ≫ F) (𝟙 Y)).symm ε
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_rightZigzag_explicit (B := SSet.QCat.{u})
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G) η' ε'
  erw [hn]
  simp only [Strict.associator_eqToIso, eqToIso.inv, eqToHom_refl, Category.id_comp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G ◁ η') ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (ε' ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G) = _
  exact congrArg₂ (· ≫ ·) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft G η') (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight ε' G)

/-- 概要：右三角恒等式があれば h Fun の左 zigzag は冪等。
方針：右三角恒等式を双圏へ戻し、一般の冪等性を表示関手で写す。
規約：左 zigzag の可逆性は不要。
使われ方：点ごとの単位条件から左三角恒等式へ進む。 -/
lemma unitLeftZigzag_idempotent {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (ε : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (G ≫ F) (𝟙 Y))
    (hR : (hoFunctor.map ((pre G).app X)).toFunctor.map η ≫
      (hoFunctor.map ((ihom Y).map G)).toFunctor.map ε =
        𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag η ε ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag η ε = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag η ε := by
  let η' : 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf X) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (𝟙 X) (F ≫ G)).symm η
  let ε' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F ⟶ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatOf Y) := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (G ≫ F) (𝟙 Y)).symm ε
  have hr : rightZigzag η' ε' = (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G)).hom ≫ (λ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G)).inv := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor Y X).map_injective
    rw [qcatRightZigzag_hom]
    simp only [Strict.rightUnitor_eqToIso, Strict.leftUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp]
    exact hR
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_leftZigzag_idempotent_of_right_triangle (B := SSet.QCat.{u})
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap G) η' ε' hr
  have hn : leftZigzag η' ε' ⊗≫ leftZigzag η' ε' =
      leftZigzag η' ε' ≫ leftZigzag η' ε' := by
    dsimp [bicategoricalComp]
    simp only [Strict.rightUnitor_eqToIso, Strict.leftUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp]
  rw [hn] at h
  have hh := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X Y).map h
  rw [CategoryTheory.Functor.map_comp] at hh
  have hl : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor X Y).map (leftZigzag η' ε') =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag η ε := qcatLeftZigzag_hom η ε
  exact (congrArg₂ (· ≫ ·) hl hl).symm.trans (hh.trans hl)

/-- 概要：構成した余単位の左 zigzag は恒等射。
方針：右三角恒等式による冪等性から、点ごとの一意性で得た可逆な左因子を消去する。
規約：結論は h Fun 全体の等式。
使われ方：指定単位を持つ随伴の左三角恒等式。 -/
lemma UnitMappingSpaceCondition.left_triangle
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)}
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaCounitData η) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag η c.counitHom = 𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) := by
  have := hη.leftZigzag_isIso c
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitLeftZigzag η c.counitHom)).1
  rw [unitLeftZigzag_idempotent η c.counitHom c.right_triangle, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
