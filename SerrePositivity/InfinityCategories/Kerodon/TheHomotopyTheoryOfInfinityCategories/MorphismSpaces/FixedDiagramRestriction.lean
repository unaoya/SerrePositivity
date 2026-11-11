module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedDiagramPrecomposition

/-!
概要：固定する部分図式の始域も変わる前合成の制限。
方針：包含の可換四角形から内部 Hom の四角形を作り、頂点の fiber へ持ち上げる。
規約：図式の固定は厳密な等式で扱う。
使われ方：Kerodon §4.6.6（Tag 04HY）、写像空間の族を部分パラメータに制限する操作。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：固定した図式の任意の部分への制限も定値である。
方針：前合成の合成則を使い、fiber の固定条件を部分図式へ写す。
規約：部分図式の射 t の単射性は不要。
使われ方：Kerodon §4.6.6（Tag 04HY）、join の片側因子における固定条件の回収。 -/
lemma fixedDiagramι_pre_factor {J K T X : SSet.{u}}
    (j : J ⟶ T) (p : J ⟶ X) (t : K ⟶ J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre j).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) ≫ (pre (t ≫ j)).app X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (t ≫ p)) := by
  rw [pre_map, NatTrans.comp_app, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
  rfl

/-- 概要：部分図式の可換四角形は固定図式の関手単体集合の制限を誘導する。
方針：通常の前合成を、引き戻した固定図式の頂点上の fiber に持ち上げる。
規約：quasicategory 性も単射性も不要。
使われ方：Kerodon §4.6.6（Tag 04HY）、両端を固定した join 図式の部分族への制限。 -/
def fixedDiagramRestriction {J K T U X : SSet.{u}}
    (j : J ⟶ T) (k : K ⟶ U) (q : U ⟶ T) (t : K ⟶ J)
    (h : k ≫ q = t ≫ j) (p : J ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre k).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (t ≫ p)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ (pre q).app X) (by
    rw [Category.assoc, ← NatTrans.comp_app, ← pre_map, h, pre_map,
      NatTrans.comp_app, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
    rfl)

/-- 概要：固定図式の制限を包含すると通常の前合成になる。
方針：fiber への持ち上げの計算則を使う。
規約：四角形の等式の証明の選択には依存しない。
使われ方：Kerodon §4.6.6（Tag 04HY）、図式の比較と制限の可換性の検査。 -/
lemma fixedDiagramRestriction_ι {J K T U X : SSet.{u}}
    (j : J ⟶ T) (k : K ⟶ U) (q : U ⟶ T) (t : K ⟶ J)
    (h : k ≫ q = t ≫ j) (p : J ⟶ X) :
    fixedDiagramRestriction j k q t h p ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre k).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (t ≫ p)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre j).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) ≫ (pre q).app X := rfl

/-- 概要：固定図式の比較と部分図式への制限は可換四角形に沿って可換。
方針：fiber の包含後に前合成の合成則と元の四角形の可換性を使う。
規約：図式の二つの包含および比較射の単射性は不要。
使われ方：Kerodon §4.6.6（Tag 04HY）、fat join 比較とパラメータ制限の両立。 -/
lemma fixedDiagramRestriction_pre_naturality {J K T U T' U' X : SSet.{u}}
    (j : J ⟶ T) (k : J ⟶ U) (q : U ⟶ T) (h : k ≫ q = j)
    (j' : K ⟶ T') (k' : K ⟶ U') (q' : U' ⟶ T') (h' : k' ≫ q' = j')
    (a : T' ⟶ T) (b : U' ⟶ U) (t : K ⟶ J)
    (hj : j' ≫ a = t ≫ j) (hk : k' ≫ b = t ≫ k)
    (hab : b ≫ q = q' ≫ a) (p : J ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramPre j k q h p ≫ fixedDiagramRestriction k k' b t hk p =
      fixedDiagramRestriction j j' a t hj p ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramPre j' k' q' h' (t ≫ p) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((pre k').app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (t ≫ p))
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramPre, Category.assoc, fixedDiagramRestriction_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, Category.assoc,
    ← NatTrans.comp_app, ← pre_map, ← Category.assoc, fixedDiagramRestriction_ι,
    Category.assoc, ← NatTrans.comp_app, ← pre_map, hab]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
