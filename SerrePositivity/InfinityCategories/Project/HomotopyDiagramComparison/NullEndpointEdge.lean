module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FiberEdgeCorrection

/-!
概要：終点で恒等の類を持つ辺を、同じ両端の fiber 内の辺へ厳密に直す。
方針：二恒等辺と元の像を持つ二単体を作り、零番ホーンを持ち上げる。
規約：底の辺は退化一単体そのもの。使われ方：根辺比較の終点を全時刻で固定する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
/-- 射影の辺の類が恒等なら、同じ両端を持つ厳密な fiber 内の辺が存在する。 -/
lemma leftFibration_correct_edge_of_null_class {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {x y : E _⦋0⦌}
    (s : SSet.Truncated.Edge (X := (truncation 2).obj E) x y)
    (b : B _⦋0⦌) (hx : p.app _ x = b) (hy : p.app _ y = b)
    (hs : SSet.Truncated.HomotopyCategory.homMk
      (⟨(s.map ((truncation 2).map p)).edge,
        (s.map ((truncation 2).map p)).src_eq.trans hx,
        (s.map ((truncation 2).map p)).tgt_eq.trans hy⟩ :
          SSet.Truncated.Edge (X := (truncation 2).obj B) b b) =
      𝟙 (SSet.HomotopyCategory.mk b)) :
    ∃ t : SSet.Truncated.Edge (X := (truncation 2).obj E) x y,
      p.app (Opposite.op ⦋1⦌) t.edge =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj B) b).edge := by
  let r : SSet.Truncated.Edge (X := (truncation 2).obj B) b b :=
    ⟨(s.map ((truncation 2).map p)).edge,
      (s.map ((truncation 2).map p)).src_eq.trans hx,
      (s.map ((truncation 2).map p)).tgt_eq.trans hy⟩
  have hfac : SSet.Truncated.HomotopyCategory.homMk
      (SSet.Truncated.Edge.id (X := (truncation 2).obj B) b) ≫
      SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id (X := (truncation 2).obj B) b) =
      SSet.Truncated.HomotopyCategory.homMk r := by
    rw [SSet.Truncated.HomotopyCategory.homMk_id, Category.id_comp]
    exact hs.symm
  obtain ⟨t₀⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hfac
  let f : SSet.Truncated.Edge (X := (truncation 2).obj E) x x :=
    SSet.Truncated.Edge.id (X := (truncation 2).obj E) x
  have hf : (f.map ((truncation 2).map p)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj B) b).edge := by
    dsimp only [f]
    rw [SSet.Truncated.Edge.map_id]
    exact congrArg (fun z ↦ (SSet.Truncated.Edge.id (X := (truncation 2).obj B) z).edge) hx
  let g : SSet.Truncated.Edge (X := (truncation 2).obj B) (p.app _ x) (p.app _ y) :=
    ⟨(SSet.Truncated.Edge.id (X := (truncation 2).obj B) b).edge,
      (SSet.Truncated.Edge.id (X := (truncation 2).obj B) b).src_eq.trans hx.symm,
      (SSet.Truncated.Edge.id (X := (truncation 2).obj B) b).tgt_eq.trans hy.symm⟩
  let t : SSet.Truncated.Edge.CompStruct (f.map ((truncation 2).map p)) g
      (s.map ((truncation 2).map p)) :=
    ⟨t₀.simplex, t₀.d₂.trans hf.symm, t₀.d₀, t₀.d₁⟩
  obtain ⟨k, tk, htk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftCompStruct p f s g t
  refine ⟨k, ?_⟩
  rw [← tk.d₀]
  calc
    _ = B.δ 0 (p.app (Opposite.op ⦋2⦌) tk.simplex) :=
      ConcreteCategory.congr_hom (p.naturality (SimplexCategory.δ 0).op) tk.simplex
    _ = g.edge := by rw [htk]; exact t.d₀

/-- Arrow として恒等の類を持つ辺からも、同じ両端の fiber 内の辺を回収する。 -/
lemma leftFibration_correct_edge_of_identity_arrow {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {x y : E _⦋0⦌} (s : E.Edge x y)
    (w : hoFunctor.obj B)
    (h : Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (s.map p).toTruncated) =
      Arrow.mk (𝟙 w)) :
    ∃ t : E.Edge x y, (t.map p).edge =
      (SSet.Edge.id (X := B) (SSet.HomotopyCategory.objEquiv w)).edge := by
  have hx : p.app _ x = SSet.HomotopyCategory.objEquiv w :=
    congrArg (fun a ↦ SSet.HomotopyCategory.objEquiv a.left) h
  have hy : p.app _ y = SSet.HomotopyCategory.objEquiv w :=
    congrArg (fun a ↦ SSet.HomotopyCategory.objEquiv a.right) h
  let r : SSet.Truncated.Edge (X := (truncation 2).obj B)
      (SSet.HomotopyCategory.objEquiv w) (SSet.HomotopyCategory.objEquiv w) :=
    ⟨(s.map p).edge, (s.map p).src_eq.trans hx, (s.map p).tgt_eq.trans hy⟩
  have hr : Arrow.mk (SSet.Truncated.HomotopyCategory.homMk r) =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk (SSet.HomotopyCategory.objEquiv w))) :=
    (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk r (s.map p).toTruncated rfl).trans h
  obtain ⟨_, _, hr⟩ := (Arrow.mk_eq_mk_iff _ _).mp hr
  have hr' : SSet.Truncated.HomotopyCategory.homMk r =
      𝟙 (SSet.HomotopyCategory.mk (SSet.HomotopyCategory.objEquiv w)) := by
    simp only [eqToHom_refl, Category.comp_id] at hr
    exact hr
  obtain ⟨t, ht⟩ := leftFibration_correct_edge_of_null_class p s.toTruncated
    (SSet.HomotopyCategory.objEquiv w) hx hy hr'
  exact ⟨SSet.Edge.ofTruncated t, ht⟩

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
