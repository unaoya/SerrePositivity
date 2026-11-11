module
public import SerrePositivity.KST.SConstruction.CoreGappedFamilies

/-! # gapped 全同値図式と core S の族の交換
概要：Ar[n] と標準単体の二つの添字を交換し、gapped 全同値図式から core S の族を作る。
方針：gapped 性の点ごとの判定と可逆な自然変換の点ごとの判定を合わせる。
規約：元の全 gapped 図式を使う。使われ方：Fiore–Pieper Proposition 4.27 の行の同型。
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

/-- 概要：関手圏の任意の端点表示の辺は点ごとに可逆性を判定できる。
方針：端点を関手頂点の同値で表示し直す。
規約：標的だけ quasicategory。使われ方：交換した族の可逆性。 -/
lemma isInvertibleFunctorEdge_iff_pointwise {K C : SSet.{u}} [Quasicategory C]
    {x y : ((ihom K).obj C) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj C)) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e ↔ ∀ k : K _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k))) := by
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K C).surjective x
  obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K C).surjective y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt e

/-- 概要：全同値図式を交換した族の全辺は可逆。
方針：Ar の各点での評価を元の全同値図式と照合する。
規約：gapped 性は不要、添字は任意。使われ方：交換した gapped 族の core への持ち上げ。 -/
lemma flipEquivalenceDiagram_edge {A K C : SSet.{u}} [Quasicategory C]
    (F : A ⟶ equivalenceDiagrams K C) (s : K _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A K C (F ≫ equivalenceDiagramι K C)).app
        (Opposite.op ⦋1⦌) s)) := by
  apply (isInvertibleFunctorEdge_iff_pointwise _).2
  intro a
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (flipFamily_evaluate (F ≫ equivalenceDiagramι K C) a)
      (Opposite.op ⦋1⦌)) s
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).2
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (F.app (Opposite.op ⦋0⦌) a)) s)

/-- 概要：gapped な全同値図式を交換すると、各頂点は gapped な Ar 図式。
方針：包含の完全性と関手圏の点ごとの判定を使う。
規約：C は安定な quasicategory。使われ方：交換した族の gapped への持ち上げ。 -/
lemma flipGappedEquivalenceDiagram_vertex {n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (F : arNerve n ⟶ equivalenceDiagrams (Δ[m] : SSet.{u}) C) (hF : IsGapped F)
    (k : (Δ[m] : SSet.{u}) _⦋0⦌) :
    IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (Δ[m] : SSet.{u}) C
        (F ≫ equivalenceDiagramι Δ[m] C)).app (Opposite.op ⦋0⦌) k)) := by
  rw [flipFamily_vertex]
  exact ((isGapped_functor_iff_pointwise _).1
    ((isGapped_equivalenceDiagramι_iff F).1 hF)) k

/-- 概要：全同値図式の圏の gapped 対象を core S の実際の族に交換する。
方針：内部 Hom を交換し、gapped 頂点と全辺の可逆性によって二段で持ち上げる。
規約：零次数も含む全ての n,m。使われ方：行の比較の順方向。 -/
def gappedEquivalenceDiagramCoreMap {n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (v : (sConstruction n (equivalenceDiagrams (Δ[m] : SSet.{u}) C)) _⦋0⦌) :
    (Δ[m] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C) : SSet.{u}) :=
  coreGappedFamilyLift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (Δ[m] : SSet.{u}) C
      (gappedDiagram v ≫ equivalenceDiagramι Δ[m] C))
    (flipGappedEquivalenceDiagram_vertex (gappedDiagram v) (gappedDiagram_isGapped v))
    (flipEquivalenceDiagram_edge (gappedDiagram v))

/-- 概要：順方向の交換を二つの包含で戻すと内部 Hom の交換そのもの。
方針：core gapped 族の持ち上げの包含公式。
規約：全単体での厳密な等号。使われ方：行の比較の逆律と自然性。 -/
lemma gappedEquivalenceDiagramCoreMap_ι {n m : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (v : (sConstruction n (equivalenceDiagrams (Δ[m] : SSet.{u}) C)) _⦋0⦌) :
    gappedEquivalenceDiagramCoreMap v ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C)).ι ≫
      (gappedSubcomplex n C).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve n) (Δ[m] : SSet.{u}) C
        (gappedDiagram v ≫ equivalenceDiagramι Δ[m] C) :=
  coreGappedFamilyLift_ι _ _ _

end SerrePositivity.KST.SConstruction
