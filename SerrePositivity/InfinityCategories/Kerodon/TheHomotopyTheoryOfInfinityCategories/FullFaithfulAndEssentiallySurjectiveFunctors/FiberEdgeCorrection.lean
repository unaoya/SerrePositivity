module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools

/-!
概要：厳密な切断により辺を fiber 内の辺へ直す補題。
方針：射影された辺を切断で持ち上げ、退化三角形の零番ホーンを持ち上げる。
規約：射影をホモトピーで置き換えず、恒等辺へ厳密に直す。
使われ方：HTT §2.2、Kerodon §4.8.4（Tag 06SQ） の fiber 内の収縮。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：切断で戻した両端が同じ始点なら、辺を同じ両端を持つ fiber 内の辺へ直せる。
方針：射影の切断による持ち上げを最初の辺、元の辺を対角とする退化三角形を持ち上げる。
規約：射影された新しい辺は標的の恒等辺そのもの。
使われ方：HTT §2.2 の厳密な切断から fiber 内のホモトピーへの移行。 -/
lemma leftFibration_correct_edge_over_identity {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) {x y : E _⦋0⦌}
    (h : SSet.Truncated.Edge (X := (truncation 2).obj E) x y)
    (hx : s.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) x) = x)
    (hy : s.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) y) = x)
    (hxy : p.app (Opposite.op ⦋0⦌) x = p.app (Opposite.op ⦋0⦌) y) :
    ∃ k : SSet.Truncated.Edge (X := (truncation 2).obj E) x y,
      p.app (Opposite.op ⦋1⦌) k.edge =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj B)
          (p.app (Opposite.op ⦋0⦌) y)).edge := by
  let l := h.map ((truncation 2).map p)
  let u₀ := l.map ((truncation 2).map s)
  let u : SSet.Truncated.Edge (X := (truncation 2).obj E) x x :=
    ⟨u₀.edge, u₀.src_eq.trans hx, u₀.tgt_eq.trans hy⟩
  have hu : p.app (Opposite.op ⦋1⦌) u.edge = l.edge := by
    change p.app (Opposite.op ⦋1⦌) (s.app (Opposite.op ⦋1⦌)
      (p.app (Opposite.op ⦋1⦌) h.edge)) = p.app (Opposite.op ⦋1⦌) h.edge
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋1⦌)) _
  let g : SSet.Truncated.Edge (X := (truncation 2).obj B)
      (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y) :=
    ⟨(SSet.Truncated.Edge.id (X := (truncation 2).obj B)
        (p.app (Opposite.op ⦋0⦌) y)).edge,
      (SSet.Truncated.Edge.id (X := (truncation 2).obj B)
        (p.app (Opposite.op ⦋0⦌) y)).src_eq.trans hxy.symm,
      (SSet.Truncated.Edge.id (X := (truncation 2).obj B)
        (p.app (Opposite.op ⦋0⦌) y)).tgt_eq⟩
  let t₀ := SSet.Truncated.Edge.CompStruct.compId l
  let t : SSet.Truncated.Edge.CompStruct (u.map ((truncation 2).map p)) g
      (h.map ((truncation 2).map p)) :=
    ⟨t₀.simplex, t₀.d₂.trans hu.symm, t₀.d₀, t₀.d₁⟩
  obtain ⟨k, tk, htk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftCompStruct p u h g t
  refine ⟨k, ?_⟩
  rw [← tk.d₀]
  calc
    _ = B.δ 0 (p.app (Opposite.op ⦋2⦌) tk.simplex) :=
      ConcreteCategory.congr_hom (p.naturality (SimplexCategory.δ 0).op) tk.simplex
    _ = g.edge := by rw [htk]; exact t.d₀

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
