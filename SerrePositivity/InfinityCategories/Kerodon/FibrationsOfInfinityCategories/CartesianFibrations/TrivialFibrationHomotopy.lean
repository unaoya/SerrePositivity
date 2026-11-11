module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FiberwiseHomotopy

/-!
概要：trivial Kan fibration の同じ射の二つの持ち上げを基底上で結ぶ。
方針：内部 Hom の射の可縮 fiber 内で実際の辺を選ぶ。
規約：比較のホモトピーそのものの基底への像が時間方向に定値。
使われ方：B1 の指定始点・境界 path を持つ輸送の一意性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：同じ基底上の二頂点は基底が恒等辺である実際の辺で結べる。
方針：指定頂点上の可縮 fiber の始対象性を使う。
規約：始域・標的の quasicategory 性は不要。
使われ方：相対的な持ち上げの比較を固定基底上で構成する。 -/
lemma exists_edge_over_trivialKanFibration {E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (x y : E _⦋0⦌)
    (h : p.app (Opposite.op ⦋0⦌) x = p.app (Opposite.op ⦋0⦌) y) :
    ∃ k : SSet.Truncated.Edge (X := (truncation 2).obj E) x y,
      p.app (Opposite.op ⦋1⦌) k.edge =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj B) (p.app (Opposite.op ⦋0⦌) y)).edge := by
  let b := p.app (Opposite.op ⦋0⦌) y
  let v₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌ := ⟨x, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]; exact h⟩
  let v₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌ := ⟨y, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]⟩
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan p b
  obtain ⟨k⟩ := (hc.isInitialVertex v₀).nonempty_edge v₁
  refine ⟨k.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)), ?_⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ p).app (Opposite.op ⦋1⦌) k.edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one b

/-- 概要：同じ射の二つの持ち上げは基底上で定値なホモトピーで結べる。
方針：内部 Hom の trivial Kan fibration の同じ頂点上で辺を選び、uncurry する。
規約：基底上の一致は raw な円柱の射の等式。
使われ方：相対 path 写像を通じた同じ輸送データの二つの実現の比較。 -/
lemma exists_homotopy_over_trivialKanFibration {A E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (f g : A ⟶ E) (h : f ≫ p = g ≫ p) :
    ∃ H : SSet.Homotopy f g,
      H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ g ≫ p := by
  obtain ⟨k, hk⟩ := exists_edge_over_trivialKanFibration ((ihom A).map p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)
    (by change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ p) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ p); rw [h])
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge k, ?_⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.simplicialHomotopyOfFunctorEdge_comp_eq_constant p (g ≫ p) k hk

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
