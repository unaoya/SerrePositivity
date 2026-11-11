module
public import SerrePositivity.KST.SConstruction.GappedEquivalenceDiagramSwap

/-! # core S の族から全同値図式の gapped 対象への交換
概要：core S への族の内部 Hom を交換し、全同値図式の圏の gapped 対象にする。
方針：各辺の評価の可逆性と、gapped 条件の点ごとの判定を使う。
規約：零対角と全押し出しを保持する。使われ方：object/core 比較の行の逆写像。
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

/-- 概要：core S の族を交換した各頂点は全同値な図式を表す。
方針：core の辺を包含し Ar の各点で評価して可逆性を得る。
規約：パラメーター K は任意。使われ方：全部分複体への逆向きの持ち上げ。 -/
lemma flipCoreGappedFamily_vertex {n : ℕ} {K C : SSet.{u}}
    (F : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C) : SSet.{u}))
    (a : (arNerve n) _⦋0⦌) :
    IsEquivalenceDiagramVertex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K (arNerve n) C
        (F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C)).ι ≫ (gappedSubcomplex n C).ι)).app
          (Opposite.op ⦋0⦌) a) := by
  intro s
  rw [flipFamily_vertex]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (F.app (Opposite.op ⦋1⦌) s).val).map
      ((truncation 2).map ((gappedSubcomplex n C).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (((F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C)).ι ≫
      (gappedSubcomplex n C).ι) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app (Opposite.op ⦋1⦌) s)) rfl).1
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge (F.app (Opposite.op ⦋1⦌) s)).map
      ((gappedSubcomplex n C).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a))

/-- 概要：core S の族を交換した図式を全同値図式の圏に持ち上げる。
方針：各頂点の全辺の可逆性による全部分複体の普遍条件。
規約：gapped 性を課す前の実際の Ar 図式。使われ方：行の逆写像の構成。 -/
def coreGappedEquivalenceDiagram {n : ℕ} {K C : SSet.{u}}
    (F : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C) : SSet.{u})) :
    arNerve n ⟶ equivalenceDiagrams K C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsEquivalenceDiagramVertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K (arNerve n) C
      (F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C)).ι ≫ (gappedSubcomplex n C).ι))
    (flipCoreGappedFamily_vertex F)

/-- 概要：逆向きの交換を含めると内部 Hom の交換そのもの。
方針：全部分複体への持ち上げの包含の式。
規約：パラメーター K は任意。使われ方：逆律と点ごとの判定。 -/
lemma coreGappedEquivalenceDiagram_ι {n : ℕ} {K C : SSet.{u}}
    (F : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C) : SSet.{u})) :
    coreGappedEquivalenceDiagram F ≫ equivalenceDiagramι K C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K (arNerve n) C
        (F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C)).ι ≫ (gappedSubcomplex n C).ι) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：core S の標準単体の族を交換した Ar 図式は gapped。
方針：包含による反映と点ごとの判定で元の gapped 頂点に帰着する。
規約：C は安定な quasicategory。使われ方：逆写像の対象条件。 -/
lemma coreGappedEquivalenceDiagram_isGapped {n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (Δ[m] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C) : SSet.{u})) :
    IsGapped (coreGappedEquivalenceDiagram F) := by
  apply (isGapped_equivalenceDiagramι_iff _).2
  rw [coreGappedEquivalenceDiagram_ι]
  apply (isGapped_functor_iff_pointwise _).2
  intro k
  rw [flipFamily_evaluate]
  exact gappedDiagram_isGapped (F.app (Opposite.op ⦋0⦌) k).val

/-- 概要：core S の標準単体の族を全同値図式の gapped 対象に戻す。
方針：交換した gapped 図式を S_n の頂点にする。
規約：選択を加えない。使われ方：行の比較の逆写像。 -/
def coreGappedEquivalenceDiagramVertex {n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : (Δ[m] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C) : SSet.{u})) :
    (sConstruction n (equivalenceDiagrams (Δ[m] : SSet.{u}) C)) _⦋0⦌ :=
  gappedObjectVertex (coreGappedEquivalenceDiagram F) (coreGappedEquivalenceDiagram_isGapped F)

/-- 概要：全同値図式の gapped 対象と core S への族は厳密に対応する。
方針：二つの包含の単射性と内部 Hom の交換の逆律を使う。
規約：全ての高次単体を持つ族の同値。使われ方：object S と core S の行の同型。 -/
def gappedEquivalenceDiagramVerticesEquiv (n m : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    (sConstruction n (equivalenceDiagrams (Δ[m] : SSet.{u}) C)) _⦋0⦌ ≃
      ((Δ[m] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C) : SSet.{u})) where
  toFun := gappedEquivalenceDiagramCoreMap
  invFun := coreGappedEquivalenceDiagramVertex
  left_inv v := by
    apply gappedDiagram_injective
    have : Mono (equivalenceDiagramι (Δ[m] : SSet.{u}) C) :=
      inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsEquivalenceDiagramVertex).ι)
    apply (cancel_mono (equivalenceDiagramι (Δ[m] : SSet.{u}) C)).1
    rw [coreGappedEquivalenceDiagramVertex, gappedDiagram_gappedObjectVertex,
      coreGappedEquivalenceDiagram_ι, gappedEquivalenceDiagramCoreMap_ι]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (Δ[m] : SSet.{u}) C).left_inv _
  right_inv F := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C)).ι).1
    apply (cancel_mono (gappedSubcomplex n C).ι).1
    rw [Category.assoc, gappedEquivalenceDiagramCoreMap_ι,
      coreGappedEquivalenceDiagramVertex, gappedDiagram_gappedObjectVertex,
      coreGappedEquivalenceDiagram_ι]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m] : SSet.{u}) (arNerve n) C).left_inv _

end SerrePositivity.KST.SConstruction
