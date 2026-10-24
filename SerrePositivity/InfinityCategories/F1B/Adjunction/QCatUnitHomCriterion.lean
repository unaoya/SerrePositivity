module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitHomCriterion
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomCorrespondence

/-!
概要：h Fun の指定単位が誘導する Hom 全単射による quasicategory 随伴の判定。
方針：二胞体の表示同値で双圏の単位判定へ移す。
規約：全ての quasicategory パラメータ A と関手 U,V について条件を課す。
使われ方：Kerodon Cor 6.2.6.5 の点ごとの写像空間条件への接続に用いる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Bicategory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
local instance unitCriterionHomCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B
local instance unitCriterionObjectQuasicategory (A : SSet.QCat.{u}) : Quasicategory A.obj :=
  A.property

/-- 概要：h Fun の指定単位が誘導するパラメータ付き Hom 写像。
方針：二胞体の表示を通して単位の whisker の公式を使う。
規約：η は余単位や三角恒等式を持つ必要がない。
使われ方：単位による写像空間比較を代数的に認識する。 -/
def qcatUnitHomMap {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (U : A ⟶ X) (V : A ⟶ Y) (α : FunctorHom (U ≫ F) V) : FunctorHom U (V ≫ G) :=
  qcatCellEquiv U (V ≫ G)
    (bicategoryUnitHomMap ((qcatCellEquiv (𝟙 X) (F ≫ G)).symm η) (qcatMap U) (qcatMap V)
      ((qcatCellEquiv (U ≫ F) V).symm α))

/-- 概要：指定単位の Hom 全単射性は二胞体の表示で変わらない。
方針：両端の表示同値による前後合成を除く。
規約：固定した A,U,V についての同値。
使われ方：双圏の判定への入力の変換。 -/
lemma qcatUnitHomMap_bijective_iff {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (U : A ⟶ X) (V : A ⟶ Y) :
    Function.Bijective (qcatUnitHomMap η U V) ↔
      Function.Bijective (bicategoryUnitHomMap
        ((qcatCellEquiv (𝟙 X) (F ≫ G)).symm η) (qcatMap U) (qcatMap V)) := by
  let s := (qcatCellEquiv (U ≫ F) V).symm
  let t := qcatCellEquiv U (V ≫ G)
  let f := bicategoryUnitHomMap ((qcatCellEquiv (𝟙 X) (F ≫ G)).symm η)
    (qcatMap U) (qcatMap V)
  change Function.Bijective (t ∘ (f ∘ s)) ↔ Function.Bijective f
  exact (Equiv.comp_bijective (f ∘ s) t).trans (Equiv.bijective_comp s f)

/-- 概要：指定単位による全パラメータの Hom 全単射から随伴を構成する。
方針：全単射条件を QCat の任意の一胞体について戻し、一般の単位判定を使う。
規約：hX と hY の Hom だけを条件にしていない。
使われ方：単位・余単位と三角恒等式を h Fun のレベルで得る。 -/
noncomputable def qcatAdjunctionOfUnitHomBijective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G))
    (hη : ∀ {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y),
      Function.Bijective (qcatUnitHomMap η U V)) : QCatAdjunction F G :=
  bicategoryAdjunctionOfUnitHomBijective ((qcatCellEquiv (𝟙 X) (F ≫ G)).symm η)
    (fun U V ↦ (qcatUnitHomMap_bijective_iff η U.hom V.hom).mp (hη U.hom V.hom))

/-- 概要：構成した随伴の単位は指定された h Fun の射。
方針：一般の単位の回収を二胞体の表示同値で移す。
規約：同型を介さない単位の等式。
使われ方：指定単位を持つ随伴の存在の判定。 -/
lemma qcatAdjunctionOfUnitHomBijective_unitHom {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G))
    (hη : ∀ {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y),
      Function.Bijective (qcatUnitHomMap η U V)) :
    (qcatAdjunctionOfUnitHomBijective η hη).unitHom = η := by
  unfold QCatAdjunction.unitHom qcatAdjunctionOfUnitHomBijective
  rw [bicategoryAdjunctionOfUnitHomBijective_unit]
  · exact (qcatCellEquiv (𝟙 X) (F ≫ G)).apply_symm_apply η
  · intro A U V
    exact (qcatUnitHomMap_bijective_iff η U.hom V.hom).mp (hη U.hom V.hom)

/-- 概要：h Fun の指定単位を持つ随伴と、全パラメータの Hom 全単射条件は同値。
方針：順方向は随伴の adjunct、逆方向は単位からの構成と単位の回収を使う。
規約：点ごとの写像空間条件からこの全パラメータ条件への橋は別に要する。
使われ方：Kerodon Cor 6.2.6.5 の逆方向の代数的な終点。 -/
lemma qcat_exists_adjunction_unitHom_iff {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) :
    (∃ a : QCatAdjunction F G, a.unitHom = η) ↔
      ∀ {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y),
        Function.Bijective (qcatUnitHomMap η U V) := by
  constructor
  · rintro ⟨a, rfl⟩ A _ U V
    exact (a.homEquiv U V).bijective
  · intro hη
    exact ⟨qcatAdjunctionOfUnitHomBijective η hη,
      qcatAdjunctionOfUnitHomBijective_unitHom η hη⟩

end SerrePositivity.InfinityCategories
