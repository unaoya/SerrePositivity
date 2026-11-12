module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedDiagramPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceRetractions

/-!
概要：固定図式上の圏論的円柱の両端の同型。
方針：円柱の射影の前合成の同値に対し、二つの端点制限を厳密な左逆として比較する。
規約：射影はエピな普遍的同値、共通部分の包含は単射。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の join の円柱からの同型。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：部分図式を延長する関手を固定図式上の fiber の頂点で表す。
方針：関手頂点の前合成を計算する。
規約：標的の quasicategory 性は不要。
使われ方：Kerodon §4.6.4（Tag 01KE） の固定図式上の比較の端点。 -/
def fixedDiagramVertex {K T X : SSet.{u}} (j : K ⟶ T) (p : K ⟶ X)
    (f : T ⟶ X) (hf : j ≫ f = p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f, by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ f) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) 0
    rw [hf, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]⟩

/-- 概要：固定図式上の圏論的円柱に延長できる二つの関手は、その fiber 内で同型。
方針：円柱の射影の前合成の同値の二つの厳密な左逆を比較して、族の頂点で評価する。
規約：共通部分の包含は単射、射影はエピな普遍的同値。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の同型を保存する方向。 -/
lemma nonempty_fixedDiagramVertexIso_of_cylinder {K T Q X : SSet.{u}}
    [Quasicategory X] (j : K ⟶ T) (k : K ⟶ Q) [Mono j] [Mono k]
    (q : Q ⟶ T) [Epi q] (hq : k ≫ q = j) (hqe : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence q)
    (a b : T ⟶ Q) (ha : j ≫ a = k) (hb : j ≫ b = k)
    (haq : a ≫ q = 𝟙 T) (hbq : b ≫ q = 𝟙 T)
    (p : K ⟶ X) (F : Q ⟶ X) (hF : k ≫ F = p) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))
      (fixedDiagramVertex j p (a ≫ F) (by rw [← Category.assoc, ha, hF]))
      (fixedDiagramVertex j p (b ≫ F) (by rw [← Category.assoc, hb, hF]))) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramPre j k q hq p
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramPre k j a ha p
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramPre k j b hb p
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_fixedDiagramPre j k q hq p hqe
  have hs : e ≫ s = 𝟙 _ := by
    dsimp [e, s]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramPre_comp]
    simpa only [haq] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramPre_id j p
  have ht : e ≫ t = 𝟙 _ := by
    dsimp [e, t]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramPre_comp]
    simpa only [hbq] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramPre_id j p
  obtain ⟨et⟩ := he.nonempty_functorIso_of_retractions s t hs ht
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app et (fixedDiagramVertex k p F hF)⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
