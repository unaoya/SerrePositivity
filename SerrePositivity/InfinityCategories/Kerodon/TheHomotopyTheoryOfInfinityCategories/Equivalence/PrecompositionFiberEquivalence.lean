module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativePrecompositionFunctorEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FiberwiseHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：前合成による射影の間の単射な同値は固定図式上でも同値。
方針：厳密な逆射を持ち上げ、逆合成を基底上の可逆ホモトピーで恒等射と結ぶ。
規約：前合成の二つの包含は単射、値域は quasicategory。
使われ方：Kerodon §4.5.3（Tag 032Y）・4.6.4（Tag 01KE） の固定図式の比較。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：前合成の射影の間の単射な同値を各図式上の fiber に制限しても同値となる。
方針：相対持ち上げで厳密な左逆を選び、固定図式上の可逆な関手の辺を fiber に制限する。
規約：j と k と e は単射、X は quasicategory、可換性は厳密な等式。
使われ方：Kerodon §4.5.3（Tag 032Y） の固定図式上の同値と §4.6.4 の太い join の比較。 -/
lemma isQCatEquivalence_vertexFiberMap_pre
    {K L M X : SSet.{u}} [Quasicategory X]
    (j : K ⟶ L) (k : K ⟶ M) [Mono j] [Mono k]
    (e : (ihom L).obj X ⟶ (ihom M).obj X) [Mono e]
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence e) (h : e ≫ (pre k).app X = (pre j).app X)
    (b : ((ihom K).obj X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap ((pre j).app X) ((pre k).app X) e h b) := by
  let p := (pre j).app X
  let q := (pre k).app X
  have hi := he.isPrecompositionEquivalence
  have := hi.hasLiftingProperty_pre j X
  let sq : CommSq (𝟙 _) e p q := ⟨by simpa only [Category.id_comp] using h.symm⟩
  let g := sq.lift
  have heg : e ≫ g = 𝟙 _ := sq.fac_left
  have hgp : g ≫ p = q := sq.fac_right
  obtain ⟨a, hai, haq⟩ := hi.exists_functorEdge_over_pre k (g ≫ e) (𝟙 _) q
    (by rw [Category.comp_id, ← Category.assoc, heg, Category.id_comp])
    (by rw [Category.assoc, h, hgp]) (by simp [q])
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge a
  have hH : H.h ≫ q = fst _ (Δ[1] : SSet.{u}) ≫ q :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.simplicialHomotopyOfFunctorEdge_comp_eq_constant q q a haq
  let HF := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberHomotopy q q (by rw [Category.assoc, h, hgp])
    (by simp) H hH b
  have hFI : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge HF x).toTruncated :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberHomotopy_isInvertible q q _ _ H hH
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible a hai) b
  let eb := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q e h b
  let gb := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q p g hgp b
  have hunit : eb ≫ gb = 𝟙 _ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q e h b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q p g hgp b) ≫ _ = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι,
      Category.assoc, heg, Category.comp_id, Category.id_comp]
  have hcounit : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (gb ≫ eb) (𝟙 _) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q p g hgp b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q e h b) (𝟙 _)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_comp]
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_id] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy HF hFI
  exact ⟨gb, ⟨eqToIso (congrArg (fun f ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) hunit)⟩,
    ⟨hcounit⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
