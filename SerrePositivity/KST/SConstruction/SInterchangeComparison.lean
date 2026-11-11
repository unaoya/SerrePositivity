module
public import SerrePositivity.KST.SConstruction.SInterchangeTranspose

/-! # 全 gapped 図式を保つ二重 S 構成の交換
概要：S_m(S_n C) の転置は Ar[n] 方向でも内部で gapped となり、S_n(S_m C) に入る。
方針：全部分複体の反映と関手圏の点ごとの gapped 判定で第二の方向を検証する。
規約：全高次単体の実際の射。使われ方：交換の厳密な逆律と構造射の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 転置の各頂点は包含後に元の族の交換を厳密に回収する。 -/
lemma sInterchangeTransposeDiagram_vertex_ι (m n : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (v : (sConstruction m (sConstruction n C)) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (sConstruction m C)).symm
        ((sInterchangeTransposeDiagram m n C).app (Opposite.op ⦋0⦌) v) ≫
      (gappedSubcomplex m C).ι =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve m) (arNerve n) C
      (gappedDiagram v ≫ (gappedSubcomplex n C).ι) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sInterchangeTransposeDiagram_ι m n C) (Opposite.op ⦋0⦌)) v
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) ((ihom (arNerve m)).obj C)).injective
  change ((ihom (arNerve n)).map (gappedSubcomplex m C).ι).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (sConstruction m C)).symm
      ((sInterchangeTransposeDiagram m n C).app (Opposite.op ⦋0⦌) v))) = _
  rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (sConstruction m C)).symm
      ((sInterchangeTransposeDiagram m n C).app (Opposite.op ⦋0⦌) v)) =
    (sInterchangeTransposeDiagram m n C).app (Opposite.op ⦋0⦌) v from
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _]
  exact h.trans (sInterchangeRawTranspose_vertex m n C v)

/-- 二重 S 構成の転置は第二の Ar 方向でも内部で gapped。 -/
lemma sInterchangeTransposeDiagram_isGapped (m n : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (v : (sConstruction m (sConstruction n C)) _⦋0⦌) :
    IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (sConstruction m C)).symm
      ((sInterchangeTransposeDiagram m n C).app (Opposite.op ⦋0⦌) v)) := by
  apply IsGapped.of_fullSubcomplex
    (fun w => IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m) C).symm w))
  change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) (sConstruction m C)).symm
    ((sInterchangeTransposeDiagram m n C).app (Opposite.op ⦋0⦌) v) ≫ (gappedSubcomplex m C).ι)
  rw [sInterchangeTransposeDiagram_vertex_ι]
  apply (isGapped_functor_iff_pointwise _).mpr
  intro a
  rw [flipFamily_evaluate]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((gappedDiagram v).app (Opposite.op ⦋0⦌) a)

/-- 全 gapped 図式を二方向の転置で交換する元の射。 -/
def sInterchange (m n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    sConstruction m (sConstruction n C) ⟶ sConstruction n (sConstruction m C) :=
  gappedFamilyLift (sInterchangeTransposeDiagram m n C)
    (sInterchangeTransposeDiagram_isGapped m n C)

/-- 二重 S の交換は包含後に構成した転置を回収する。 -/
lemma sInterchange_ι (m n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    sInterchange m n C ≫ (gappedSubcomplex n (sConstruction m C)).ι =
      sInterchangeTransposeDiagram m n C := gappedFamilyLift_ι _ _

/-- 二重 S の交換の二つの包含への合成は二重内部 Hom の交換そのもの。 -/
lemma sInterchange_double_ι (m n : ℕ) (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    (sInterchange m n C ≫ (gappedSubcomplex n (sConstruction m C)).ι) ≫
      (ihom (arNerve n)).map (gappedSubcomplex m C).ι =
    ((gappedSubcomplex m (sConstruction n C)).ι ≫
      (ihom (arNerve m)).map (gappedSubcomplex n C).ι) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve m) (arNerve n) C).hom := by
  rw [sInterchange_ι, sInterchangeTransposeDiagram_ι]
  rfl

end SerrePositivity.KST.SConstruction
