module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatMappingSpace

/-!
概要：Cat_∞ の写像空間比較の零単体と豊穣関手に関する自然性。
方針：F1 の全次数の自然性と通常の射の比較を QCat に適用する。
規約：逆射の選択に依存せず、元の標準比較射そのものを比較する。
使われ方：Cat_∞ の写像空間の普遍性を実際の関手空間へ移す。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：関手 core の零単体は Cat_∞ の同じ関手の辺へ写る。
方針：QCat に F1 の通常の射の比較公式を適用する。
規約：指定された元の関手の辺との厳密な等式を返す。
使われ方：写像空間の比較と辺の表示の整合性。 -/
lemma catInfinityMappingComparison_ordinary {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}} (f : X ⟶ Y) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityMappingComparison X Y).app (Opposite.op ⦋0⦌)
      (ULift.up (SimplicialCategory.homEquiv' X Y f))).val = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdge f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_ordinary f

/-- 概要：Cat_∞ の標準比較は豊穣自己関手の Hom 上の作用と可換。
方針：F1 の豊穣自然性の全次数の可換図式を QCat に適用する。
規約：端点の正規化は coherentPinchedHomMap に含まれる。
使われ方：Cat_∞ の図式の操作と関手 core の操作を対応させる。 -/
lemma catInfinityMappingComparison_enriched_naturality
    (F : EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityMappingComparison X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedHomMap F X Y =
      (SSet.uliftFunctor.{u + 1, u}).map (F.map X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catInfinityMappingComparison (F.obj X) (F.obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_enriched_naturality F X Y

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
