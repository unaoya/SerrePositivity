module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FixedCosliceReindexUncurry
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionFixedReindexSwap

/-! # 対称 span の余錐空間の交換作用

概要：同じ辺を二枝に使う span の余錐空間に、枝を交換する対合を構成する。
方針：固定図式内の再添字付けを特殊化し、二枝への制限と Hom 表示での作用を計算する。
規約：自己写像の型には図式の輸送を残さない。使われ方：二枝の引き戻しからループ反転への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：同じ辺を二枝に使う span の余錐空間の二枝交換。
方針：二枝交換が図式を固定する等号で同じ図式上の自己作用を作る。
規約：辺の終点の零対象性は不要。使われ方：対称な suspension の写像空間での作用。 -/
def symmetricCoconeSwap {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCoconeMappingReindex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeSpan_self_swap f) y

/-- 概要：対称 span の二枝交換は二度で恒等になる。
方針：形状の交換の対合性を固定図式の再添字付けへ適用する。
規約：値域の充填性は不要。使われ方：交換作用の自己同型性。 -/
lemma symmetricCoconeSwap_comp_self {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    symmetricCoconeSwap f y ≫ symmetricCoconeSwap f y = 𝟙 _ :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCoconeMappingReindex_comp_self _ _ _ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_comp_self y

/-- 概要：対称 span の二枝交換による余錐空間の自己同型。
方針：交換自体を逆に使う。
規約：実際の単体集合の同型。使われ方：写像空間の自己作用の比較。 -/
def symmetricCoconeSwapIso {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y where
  hom := symmetricCoconeSwap f y
  inv := symmetricCoconeSwap f y
  hom_inv_id := symmetricCoconeSwap_comp_self f y
  inv_hom_id := symmetricCoconeSwap_comp_self f y

/-- 概要：交換後の余錐の第一枝は元の第二枝である。
方針：自己作用を展開して joinMap の合成に枝の交換則を使う。
規約：余錐族のパラメータは任意。使われ方：二枝の引き戻し模型での作用。 -/
lemma symmetricCoconeSwap_left {X T : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌)
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap horn₂₀.ι₀₁ (𝟙 T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry
      ((a ≫ symmetricCoconeSwap f y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap horn₂₀.ι₀₂ (𝟙 T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry
      (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) y) := by
  rw [symmetricCoconeSwap, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCoconeMappingReindex_uncurry, ← Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_left, Category.comp_id]

/-- 概要：交換後の余錐の第二枝は元の第一枝である。
方針：自己作用を展開して第二枝の交換則を使う。
規約：余錐族のパラメータは任意。使われ方：二枝の引き戻し模型での作用。 -/
lemma symmetricCoconeSwap_right {X T : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌)
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap horn₂₀.ι₀₂ (𝟙 T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry
      ((a ≫ symmetricCoconeSwap f y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap horn₂₀.ι₀₁ (𝟙 T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry
      (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) y) := by
  rw [symmetricCoconeSwap, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCoconeMappingReindex_uncurry, ← Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_right, Category.comp_id]

/-- 概要：対称 span の余錐空間の交換は Hom 表示で標準頂点自己同型の前合成となる。
方針：固定図式の再添字付けの Hom への作用を二枝交換へ特殊化する。
規約：値域は quasicategory、c は指定した図式の余極限余錐。使われ方：交換作用と負号の比較。 -/
lemma symmetricCoconeSwap_piZero {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (y : X _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y (SSet.mapπ₀ (symmetricCoconeSwap f y) a) =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCoconeReindexVertexIso c hc _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeSpan_self_swap f) _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_comp_self).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y a :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeMappingSpacePiZeroEquiv_reindexFixed c hc _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeSpan_self_swap f)
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_comp_self y a

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
