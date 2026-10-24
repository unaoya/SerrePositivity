module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitHomLeftNaturality
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaCounitData

/-!
概要：右三角恒等式から左 zigzag の単位 Hom 比較による像を計算する。
方針：始域側の自然性と F に沿う前合成に右三角恒等式を適用する。
規約：左 zigzag 自体が恒等であることはここでは仮定しない。
使われ方：B1 の各点の単射性から左三角恒等式へ進む代数的な式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：指定単位・余単位の左 zigzag を h Fun の自己準同型として表す。
方針：単位の F による後合成と余単位の F に沿う前合成を続ける。
規約：三角恒等式は要求しない。
使われ方：左三角恒等式の検証対象。 -/
def unitLeftZigzag {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (ε : FunctorHom (G ≫ F) (𝟙 Y)) : FunctorHom F F :=
  (hoFunctor.map ((ihom X).map F)).toFunctor.map η ≫
    (hoFunctor.map ((pre F).app Y)).toFunctor.map ε

/-- 概要：右三角恒等式があれば左 zigzag の単位比較による像は恒等射の像と同じ。
方針：始域側の自然性と右三角恒等式の F に沿う制限を使う。
規約：h Fun 全体の等式。単射性は別に要する。
使われ方：各点の比較の単射性を左 zigzag に適用する準備。 -/
lemma qcatUnitHomMap_leftZigzag {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (ε : FunctorHom (G ≫ F) (𝟙 Y))
    (hR : (hoFunctor.map ((pre G).app X)).toFunctor.map η ≫
      (hoFunctor.map ((ihom Y).map G)).toFunctor.map ε =
        𝟙 (HomotopyCategory.mk (functorVertex G))) :
    qcatUnitHomMap η (𝟙 X) F (unitLeftZigzag η ε) =
      qcatUnitHomMap η (𝟙 X) F (𝟙 (HomotopyCategory.mk (functorVertex F))) := by
  have hq : qcatUnitHomMap η G (𝟙 Y) ε =
      𝟙 (HomotopyCategory.mk (functorVertex G)) := by
    rw [qcatUnitHomMap_formula]
    exact hR
  have hp := qcatUnitHomMap_precomp η F G (𝟙 Y) ε
  rw [hq, CategoryTheory.Functor.map_id] at hp
  change qcatUnitHomMap η (𝟙 X) F
    ((hoFunctor.map ((ihom X).map F)).toFunctor.map η ≫
      (hoFunctor.map ((pre F).app Y)).toFunctor.map ε) = _
  erw [qcatUnitHomMap_naturality_left (F := F) (G := G) η
    (U := F ≫ G) (U' := 𝟙 X) (V := F) η
    ((hoFunctor.map ((pre F).app Y)).toFunctor.map ε)]
  change η ≫ qcatUnitHomMap η (F ≫ G) F
    ((hoFunctor.map ((pre F).app Y)).toFunctor.map ε) = _
  erw [hp, Category.comp_id]
  rw [qcatUnitHomMap_formula]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hpre : (pre (𝟙 X)).app X = 𝟙 ((ihom X).obj X) := by
    rw [pre_id]
    rfl
  have he := congrArg (fun q : (ihom X).obj X ⟶ (ihom X).obj X ↦
    (hoFunctor.map q).toFunctor) hpre
  rw [CategoryTheory.Functor.map_id] at he
  have hh := CategoryTheory.Functor.congr_hom he η
  simpa only [CategoryTheory.Functor.map_id, eqToHom_refl, Category.id_comp,
    Category.comp_id, Cat.Hom.id_map] using hh.symm

/-- 概要：構成した余単位の左 zigzag は指定単位の比較で恒等射と同じ像を持つ。
方針：同じ比較データで証明した右三角恒等式を使う。
規約：左三角恒等式自体はまだ結論しない。
使われ方：点ごとの単射性による左 zigzag の検証。 -/
lemma UnitCommaCounitData.leftZigzag_image
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : FunctorHom (𝟙 X) (F ≫ G)}
    (c : UnitCommaCounitData η) :
    qcatUnitHomMap η (𝟙 X) F (unitLeftZigzag η c.counitHom) =
      qcatUnitHomMap η (𝟙 X) F (𝟙 (HomotopyCategory.mk (functorVertex F))) :=
  qcatUnitHomMap_leftZigzag η c.counitHom c.right_triangle

end SerrePositivity.InfinityCategories
