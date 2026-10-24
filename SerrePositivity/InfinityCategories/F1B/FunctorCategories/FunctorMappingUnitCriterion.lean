module

public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.MappingSpaceHom
public import SerrePositivity.InfinityCategories.F1B.Adjunction.QCatUnitHomCriterion

/-!
概要：非定値の関手間の pinched 写像空間比較から指定単位を持つ随伴を構成する。
方針：比較の零単体での公式から Hom 上の単位写像を認識し、全単射性を移す。
規約：比較の同値性は全てのパラメータ A と任意の U,V に課す。各点の条件への還元は別段階。
使われ方：写像空間の条件と、既存の単位による全パラメータ Hom 判定との橋。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：関手間の写像空間比較が単位の公式を表せば、単位の Hom 写像は全単射。
方針：全ての代表辺での公式から比較の Hom への移送を同定し、その全単射性を使う。
規約：固定した A,U,V についての主張。単位が随伴の単位であるとは仮定しない。
使われ方：写像空間比較の同値性から単位判定の仮定を供給する。 -/
lemma qcatUnitHomMap_bijective_of_mappingSpace {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (U : A ⟶ X) (V : A ⟶ Y)
    (q : pinchedHom (functorVertex (U ≫ F)) (functorVertex V) ⟶
      pinchedHom (functorVertex U) (functorVertex (V ≫ G)))
    (hq : IsSimplicialHomotopyEquivalence q)
    (hqη : ∀ s : (pinchedHom (functorVertex (U ≫ F)) (functorVertex V)) _⦋0⦌,
      qcatUnitHomMap η U V
        (SSet.Truncated.HomotopyCategory.homMk
          (pinchedHomVertexEquiv (functorVertex (U ≫ F)) (functorVertex V) s)) =
        SSet.Truncated.HomotopyCategory.homMk
          (pinchedHomVertexEquiv (functorVertex U) (functorVertex (V ≫ G))
            (q.app (Opposite.op ⦋0⦌) s))) :
    Function.Bijective (qcatUnitHomMap η U V) := by
  rw [mappingSpaceHomMap_eq_of_homMk q (qcatUnitHomMap η U V) hqη]
  exact mappingSpaceHomMap_bijective q hq

/-- 概要：全パラメータの単位を表す pinched 写像空間同値から随伴を構成する。
方針：各比較から Hom 全単射を得て、指定単位の判定を適用する。
規約：A と U,V 全ての比較を入力とする。各点だけからこの族を作る工程はまだ必要。
使われ方：非定値関手間の写像空間比較を余単位・三角恒等式へ接続する。 -/
noncomputable def qcatAdjunctionOfUnitMappingEquivalences {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G))
    (q : ∀ {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y),
      pinchedHom (functorVertex (U ≫ F)) (functorVertex V) ⟶
        pinchedHom (functorVertex U) (functorVertex (V ≫ G)))
    (hq : ∀ {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y),
      IsSimplicialHomotopyEquivalence (q U V))
    (hqη : ∀ {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y)
      (s : (pinchedHom (functorVertex (U ≫ F)) (functorVertex V)) _⦋0⦌),
      qcatUnitHomMap η U V
        (SSet.Truncated.HomotopyCategory.homMk
          (pinchedHomVertexEquiv (functorVertex (U ≫ F)) (functorVertex V) s)) =
        SSet.Truncated.HomotopyCategory.homMk
          (pinchedHomVertexEquiv (functorVertex U) (functorVertex (V ≫ G))
            ((q U V).app (Opposite.op ⦋0⦌) s))) : QCatAdjunction F G :=
  qcatAdjunctionOfUnitHomBijective η
    (fun U V ↦ qcatUnitHomMap_bijective_of_mappingSpace η U V (q U V) (hq U V) (hqη U V))

/-- 概要：写像空間比較から構成した随伴の単位は指定した η。
方針：全パラメータの Hom 判定の単位の回収を使う。
規約：単位は h Fun の射として等しい。
使われ方：指定単位による写像空間判定の結論。 -/
lemma qcatAdjunctionOfUnitMappingEquivalences_unitHom {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G))
    (q : ∀ {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y),
      pinchedHom (functorVertex (U ≫ F)) (functorVertex V) ⟶
        pinchedHom (functorVertex U) (functorVertex (V ≫ G)))
    (hq : ∀ {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y),
      IsSimplicialHomotopyEquivalence (q U V))
    (hqη : ∀ {A : SSet.{u}} [Quasicategory A] (U : A ⟶ X) (V : A ⟶ Y)
      (s : (pinchedHom (functorVertex (U ≫ F)) (functorVertex V)) _⦋0⦌),
      qcatUnitHomMap η U V
        (SSet.Truncated.HomotopyCategory.homMk
          (pinchedHomVertexEquiv (functorVertex (U ≫ F)) (functorVertex V) s)) =
        SSet.Truncated.HomotopyCategory.homMk
          (pinchedHomVertexEquiv (functorVertex U) (functorVertex (V ≫ G))
            ((q U V).app (Opposite.op ⦋0⦌) s))) :
    (qcatAdjunctionOfUnitMappingEquivalences η q hq hqη).unitHom = η :=
  qcatAdjunctionOfUnitHomBijective_unitHom η
    (fun U V ↦ qcatUnitHomMap_bijective_of_mappingSpace η U V (q U V) (hq U V) (hqη U V))

end SerrePositivity.InfinityCategories
