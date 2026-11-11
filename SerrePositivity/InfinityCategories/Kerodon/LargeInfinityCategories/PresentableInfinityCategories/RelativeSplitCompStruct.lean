module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeSplitTriangleLift
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SplitTriangleDecomposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeRestrictionTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction

/-!
概要：元の増大余錐を保ち、前置部分の分裂三角形を全前置図式の分裂合成構造へ持ち上げる。
方針：恒等長辺を固定する全単体の持ち上げと、同じ二単体の分解を組み合わせる。
規約：固定図式の等式による正規化を含め、全二単体の像を厳密に保持する。
使われ方：可算交互構成の各有限段階の延長。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：分裂合成構造を、元の基点の恒等長辺を保って全単体ごと持ち上げる。
方針：二単体を長辺で持ち上げ、同じ二単体を合成構造に分解する。
規約：二単体の像は元の合成構造の単体そのもの。
使われ方：coslice 制限を通した全前置図式の分裂比較。 -/
lemma exists_splitCompStruct_lift {X Y : SSet.{u}} (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (x : X _⦋0⦌) {y : Y _⦋0⦌} {e : Y.Edge (p.app _ x) y}
    {r : Y.Edge y (p.app _ x)} (T : e.CompStruct r (SSet.Edge.id (p.app _ x))) :
    ∃ (y' : X _⦋0⦌) (e' : X.Edge x y') (r' : X.Edge y' x)
      (T' : e'.CompStruct r' (SSet.Edge.id x)), p.app _ T'.simplex = T.simplex := by
  obtain ⟨S, hpS, hS⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_splitTriangle_lift p x T.simplex T.d₁
  obtain ⟨y', e', r', T', hT'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_splitCompStruct_of_identity_longEdge x S hS
  exact ⟨y', e', r', T', by rw [hT']; exact hpS⟩

/-- 概要：正規化された前置部分の二単体を、同じ元の増大余錐の分裂合成へ戻す。
方針：元の全余錐値の等式で基点を揃え、right anodyne 制限で持ち上げる。
規約：既存の全余錐と固定図式の等式を保持する。
使われ方：偶数前置図式の因子化を全交互前置図式へ延長する。 -/
lemma exists_normalizedCoslice_splitCompStruct {K L C : SSet.{u}} [Quasicategory C]
    (j : K ⟶ L) [Mono j] (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j)
    (F : L ⟶ C) (p : K ⟶ C) (hF : j ≫ F = p)
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋0⦌) (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) _⦋0⦌)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap j (𝟙 Δ[0]) ≫ c.val = b.val)
    (T : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) _⦋2⦌)
    (hT : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).δ 1 T = (SSet.Edge.id b).edge) :
    ∃ (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).Edge c d)
      (r : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).Edge d c) (S : e.CompStruct r (SSet.Edge.id c)),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction F j hF).app _ S.simplex = T := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction F j hF
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration F j hj
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict F j))
      (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations _)⟩
  have hbase : q.app (Opposite.op ⦋0⦌) c = b := by
    apply Subtype.ext
    change ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hF)).hom.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict F j).app (Opposite.op ⦋0⦌) c)).val = b.val
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnder_eqToIso_val hF]
    exact hc
  have hlong : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).δ 1 T = (SSet.Edge.id (q.app (Opposite.op ⦋0⦌) c)).edge := by
    rw [hbase]
    exact hT
  obtain ⟨S, hqS, hS⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_splitTriangle_lift q c T hlong
  obtain ⟨d, e, r, S', hS'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_splitCompStruct_of_identity_longEdge c S hS
  exact ⟨d, e, r, S', by rw [hS']; exact hqS⟩

/-- 概要：全二単体の像の等式は分裂三角形の中間頂点も厳密に保つ。
方針：最初の辺の面とその終点の二つの自然性を使う。
規約：全単体の等式から回収し、頂点比較を入力にしない。
使われ方：次の元の表示段の全 coslice 頂点の同定。 -/
lemma compStruct_middle_image_of_simplex_eq {X Y : SSet.{u}} (p : X ⟶ Y)
    {a b c : X _⦋0⦌} {a' b' c' : Y _⦋0⦌}
    {e : X.Edge a b} {r : X.Edge b c} {f : X.Edge a c}
    {e' : Y.Edge a' b'} {r' : Y.Edge b' c'} {f' : Y.Edge a' c'}
    (T : e.CompStruct r f) (U : e'.CompStruct r' f')
    (h : p.app _ T.simplex = U.simplex) : p.app _ b = b' := by
  have he := congrArg (fun z ↦ Y.δ 2 z) h
  rw [← SSet.δ_naturality_apply, T.d₂, U.d₂] at he
  have hv := congrArg (fun z ↦ Y.δ 0 z) he
  rw [← SSet.δ_naturality_apply, e.tgt_eq, e'.tgt_eq] at hv
  exact hv

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
