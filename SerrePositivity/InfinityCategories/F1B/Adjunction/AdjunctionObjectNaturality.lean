module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantObjectNaturality
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalComposition
public import SerrePositivity.InfinityCategories.F1B.Adjunction.AdjunctionMappingSpaces

/-!
概要：随伴の区間写像空間の比較射の対象変数に関する自然性。
方針：任意のパラメータ族の adjunct の公式に h Fun の自然性を適用する。
規約：hX・hY の射による前後合成との可換性を実際の単体的ホモトピーで述べる。
使われ方：Kerodon Prop 6.2.1.17 の自然な写像空間比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.QCatAdjunction

/-- 概要：随伴比較は終域変数の後合成とホモトピーまで可換。
方針：二つの経路が表す h Fun の射を adjunct の自然性で比較する。
規約：δ は hY の任意の射。パラメータは普遍族の Kan 複体。
使われ方：写像空間の終域変数に関する自然性。 -/
lemma intervalMap_naturality_right {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G)
    (x : X _⦋0⦌) {y y' : Y _⦋0⦌}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj Y) ⟶ HomotopyCategory.mk y') :
    Nonempty (SSet.Homotopy
      (intervalPostcompose (F.app (Opposite.op ⦋0⦌) x) δ ≫ a.intervalMap x y')
      (a.intervalMap x y ≫ intervalPostcompose x ((hoFunctor.map G).toFunctor.map δ))) := by
  apply intervalFamilyHom_eq_imp_homotopy
  rw [intervalMap_family, intervalPostcompose_family, intervalPostcompose_hom,
    intervalMap_hom, constantHomEquiv_naturality_right]

/-- 概要：随伴比較は始域変数の前合成とホモトピーまで可換。
方針：二つの経路が表す h Fun の射を adjunct の自然性で比較する。
規約：γ は hX の任意の射。前合成は始域変数に反変。
使われ方：写像空間の始域変数に関する自然性。 -/
lemma intervalMap_naturality_left {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G)
    {x' x : X _⦋0⦌} (y : Y _⦋0⦌)
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x) :
    Nonempty (SSet.Homotopy
      (intervalPrecompose y ((hoFunctor.map F).toFunctor.map γ) ≫ a.intervalMap x' y)
      (a.intervalMap x y ≫ intervalPrecompose (G.app (Opposite.op ⦋0⦌) y) γ)) := by
  apply intervalFamilyHom_eq_imp_homotopy
  rw [intervalMap_family, intervalPrecompose_family, intervalPrecompose_hom,
    intervalMap_hom, constantHomEquiv_naturality_left]
  rfl

end SerrePositivity.InfinityCategories.QCatAdjunction
