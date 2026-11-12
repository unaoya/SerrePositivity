module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PullbackInvertibleEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EdgeRepresentativeLift
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBaseChange

/-!
概要：引き戻しの指定した二頂点間で、厳密に整合する辺を貼り合わせる。
方針：辺の Yoneda 表示を実引き戻しへ持ち上げ、必要な代表修正には公開 API を使う。
規約：両端点と第二成分の辺を固定する。
使われ方：compact 成分の代表を元の引き戻しの頂点同型として比較する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：厳密に同じ像を持つ二成分の辺を元の引き戻しで貼り合わせる。
方針：Δ[1] の二射を持ち上げ、両端を射影で検証する。
規約：辺のホモトピー類だけでなく実際の二成分を保持する。
使われ方：整合する成分同型からの引き戻し内の同型。 -/
def pullbackEdgeOfComponents {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    {x y : (pullback p q) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E)
      ((pullback.fst p q).app _ x) ((pullback.fst p q).app _ y))
    (g : SSet.Truncated.Edge (X := (truncation 2).obj D)
      ((pullback.snd p q).app _ x) ((pullback.snd p q).app _ y))
    (h : p.app (Opposite.op ⦋1⦌) f.edge = q.app (Opposite.op ⦋1⦌) g.edge) :
    SSet.Truncated.Edge (X := (truncation 2).obj (pullback p q)) x y := by
  let a : (Δ[1] : SSet.{u}) ⟶ pullback p q := pullback.lift
    (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge)
    (by rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h])
  have hsrc : stdSimplex.δ 1 ≫ a = SSet.yonedaEquiv.symm x := by
    apply pullback.hom_ext
    · simp only [a, Category.assoc, pullback.lift_fst,
        stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
      exact congrArg SSet.yonedaEquiv.symm f.src_eq
    · simp only [a, Category.assoc, pullback.lift_snd,
        stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
      exact congrArg SSet.yonedaEquiv.symm g.src_eq
  have htgt : stdSimplex.δ 0 ≫ a = SSet.yonedaEquiv.symm y := by
    apply pullback.hom_ext
    · simp only [a, Category.assoc, pullback.lift_fst,
        stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
      exact congrArg SSet.yonedaEquiv.symm f.tgt_eq
    · simp only [a, Category.assoc, pullback.lift_snd,
        stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
      exact congrArg SSet.yonedaEquiv.symm g.tgt_eq
  refine ⟨SSet.yonedaEquiv a, ?_, ?_⟩
  · change (pullback p q).δ 1 (SSet.yonedaEquiv a) = x
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv hsrc
  · change (pullback p q).δ 0 (SSet.yonedaEquiv a) = y
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv htgt

/-- 概要：貼り合わせた辺の第一射影は指定した辺そのもの。
方針：Yoneda と引き戻しの第一射影公式を使う。
規約：端点の証明を含めた辺の等式。
使われ方：成分のホモトピー類と可逆性の回収。 -/
lemma pullbackEdgeOfComponents_fst {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    {x y : (pullback p q) _⦋0⦌} (f) (g) (h) :
    (pullbackEdgeOfComponents (x := x) (y := y) p q f g h).map
      ((truncation 2).map (pullback.fst p q)) = f := by
  apply SSet.Truncated.Edge.ext
  change (pullback.fst p q).app _ (SSet.yonedaEquiv _) = f.edge
  rw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
  exact SSet.yonedaEquiv.apply_symm_apply f.edge

/-- 概要：貼り合わせた辺の第二射影は指定した辺そのもの。
方針：Yoneda と引き戻しの第二射影公式を使う。
規約：端点の証明を含めた辺の等式。
使われ方：成分のホモトピー類と可逆性の回収。 -/
lemma pullbackEdgeOfComponents_snd {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    {x y : (pullback p q) _⦋0⦌} (f) (g) (h) :
    (pullbackEdgeOfComponents (x := x) (y := y) p q f g h).map
      ((truncation 2).map (pullback.snd p q)) = g := by
  apply SSet.Truncated.Edge.ext
  change (pullback.snd p q).app _ (SSet.yonedaEquiv _) = g.edge
  rw [← SSet.yonedaEquiv_comp, pullback.lift_snd]
  exact SSet.yonedaEquiv.apply_symm_apply g.edge

/-- 概要：第二成分の辺の像を第一成分の像と同じ両端で表示する。
方針：右写像空間の公開された引き戻し基底比較で端点を合わせる。
規約：元の単体としての辺は変更しない。
使われ方：両成分の像のホモトピー類の整合条件。 -/
def pullbackSecondEdgeInBase {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    {x y : (pullback p q) _⦋0⦌}
    (g : SSet.Truncated.Edge (X := (truncation 2).obj D)
      ((pullback.snd p q).app _ x) ((pullback.snd p q).app _ y)) :
    SSet.Truncated.Edge (X := (truncation 2).obj B)
      (p.app _ ((pullback.fst p q).app _ x))
      (p.app _ ((pullback.fst p q).app _ y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackBaseMap p q x y).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).symm g))

/-- 概要：像の類が整合する二成分の辺は、第一成分の類を保って引き戻しの辺になる。
方針：公開された inner 射の辺代表修正で像を厳密に合わせ、実引き戻しに貼り合わせる。
規約：第二成分の実際の辺と元の両端点を保持する。
使われ方：compact 成分の同型を元の引き戻しの中へ持ち上げる。 -/
lemma exists_pullbackEdge_of_component_classes {E D B : SSet.{u}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p]
    {x y : (pullback p q) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E)
      ((pullback.fst p q).app _ x) ((pullback.fst p q).app _ y))
    (g : SSet.Truncated.Edge (X := (truncation 2).obj D)
      ((pullback.snd p q).app _ x) ((pullback.snd p q).app _ y))
    (h : SSet.Truncated.HomotopyCategory.homMk (f.map ((truncation 2).map p)) =
      SSet.Truncated.HomotopyCategory.homMk (pullbackSecondEdgeInBase p q g)) :
    ∃ e : SSet.Truncated.Edge (X := (truncation 2).obj (pullback p q)) x y,
      SSet.Truncated.HomotopyCategory.homMk
          (e.map ((truncation 2).map (pullback.fst p q))) =
        SSet.Truncated.HomotopyCategory.homMk f ∧
      e.map ((truncation 2).map (pullback.snd p q)) = g := by
  obtain ⟨f', hm, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanEdgeRepresentative_lift p f
    (pullbackSecondEdgeInBase p q g) h
  change p.app (Opposite.op ⦋1⦌) f'.edge = q.app (Opposite.op ⦋1⦌) g.edge at hm
  exact ⟨pullbackEdgeOfComponents p q f' g hm,
    (congrArg SSet.Truncated.HomotopyCategory.homMk
      (pullbackEdgeOfComponents_fst p q f' g hm)).trans hf,
    pullbackEdgeOfComponents_snd p q f' g hm⟩

/-- 概要：像の類が整合する可逆な二成分は元の引き戻しの頂点同型を与える。
方針：両成分の類を保った辺を構成し、二射影による可逆性の反映を使う。
規約：元の引き戻しの二頂点間で結論する。
使われ方：小さい compact 代表族の被覆の検証。 -/
lemma exists_pullbackVertexIso_of_component_edge_classes {E D B : SSet.{u}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p]
    {x y : (pullback p q) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E)
      ((pullback.fst p q).app _ x) ((pullback.fst p q).app _ y))
    (g : SSet.Truncated.Edge (X := (truncation 2).obj D)
      ((pullback.snd p q).app _ x) ((pullback.snd p q).app _ y))
    (h : SSet.Truncated.HomotopyCategory.homMk (f.map ((truncation 2).map p)) =
      SSet.Truncated.HomotopyCategory.homMk (pullbackSecondEdgeInBase p q g))
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge f) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge g) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) := by
  obtain ⟨e, he, hs⟩ := exists_pullbackEdge_of_component_classes p q f g h
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pullback_isInvertibleEdge_of_projections p q e
    · change IsIso (SSet.Truncated.HomotopyCategory.homMk _)
      rw [he]
      exact hf
    · exact hs.symm ▸ hg
  exact ⟨asIso (SSet.Truncated.HomotopyCategory.homMk e)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
