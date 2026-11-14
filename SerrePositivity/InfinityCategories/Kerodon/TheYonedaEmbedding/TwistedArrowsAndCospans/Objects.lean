module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Edges

/-!
概要：cocartesian lift の選択と fiber の対象の移送。
方針：指定始点から持ち上げた辺の終点を標的の fiber に入れる。
規約：ここでの移送は対象の写像であり、単体集合の射ではない。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS） の transport 関手の存在証明の頂点段階。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：指定始点から底の辺に沿う cocartesian lift のデータ。
方針：標的 fiber の対象と、両端と底の値を固定した cocartesian 辺を保持する。
規約：辺は一単体、fiber は既存の vertexFiber を使う。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の対象の選択。 -/
structure CocartesianEdgeLift {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e)) _⦋0⦌) where
  /-- 標的 fiber の対象。 -/
  target : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 0 e)) _⦋0⦌
  /-- 選択された lift の一単体。 -/
  edge : X _⦋1⦌
  /-- lift の始点は指定した対象。 -/
  source_eq : X.δ 1 edge = x.val
  /-- lift の終点は標的 fiber の対象。 -/
  target_eq : X.δ 0 edge = target.val
  /-- 底に射影すると元の辺。 -/
  over : p.app (Opposite.op ⦋1⦌) edge = e
  /-- 選択された辺の cocartesian 性。 -/
  isCocartesian : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p edge

/-- 概要：cocartesian fibration では各始点からの lift の型は非空。
方針：定義の存在条件を使い、自然性で終点が標的 fiber に入ることを示す。
規約：底の quasicategory 性を仮定しない。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS） の頂点での存在。 -/
lemma nonempty_cocartesianEdgeLift {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (e : B _⦋1⦌)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e)) _⦋0⦌) : Nonempty (CocartesianEdgeLift p e x) := by
  have hx : p.app (Opposite.op ⦋0⦌) x.val = B.δ 1 e := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero] using x.property
  have hs : stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm e =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x.val) := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, hx]
  obtain ⟨f, hf, hfp, hfc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration.mem (p := p) |>.2 x.val
    (SSet.yonedaEquiv.symm e) hs
  let a := SSet.yonedaEquiv f
  have ha : p.app (Opposite.op ⦋1⦌) a = e := by
    rw [← SSet.yonedaEquiv_comp, hfp, Equiv.apply_symm_apply]
  have hat : p.app (Opposite.op ⦋0⦌) (X.δ 0 a) = B.δ 0 e := by
    calc
      _ = B.δ 0 (p.app (Opposite.op ⦋1⦌) a) :=
        ConcreteCategory.congr_hom (p.naturality (SimplexCategory.δ 0).op) a
      _ = B.δ 0 e := by rw [ha]
  let y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 0 e)) _⦋0⦌ :=
    ⟨X.δ 0 a, by simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero] using hat⟩
  refine ⟨⟨y, a, ?_, rfl, ha, hfc⟩⟩
  rw [← stdSimplex.yonedaEquiv_δ_comp, hf, Equiv.apply_symm_apply]

/-- 概要：cocartesian lift を一つ選ぶ。
方針：非空性から Classical.choice で選択する。
規約：関手性や選択からの独立性はこの選択には含めない。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS） の transport の頂点部分。 -/
noncomputable def chooseCocartesianEdgeLift {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (e : B _⦋1⦌)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e)) _⦋0⦌) : CocartesianEdgeLift p e x :=
  Classical.choice (nonempty_cocartesianEdgeLift p e x)

/-- 概要：辺に沿って始点の fiber の対象を終点の fiber へ移す。
方針：選択した cocartesian lift の終点を取る。
規約：写像の定義域と値域は零単体の型。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport 関手の対象部分の準備。 -/
noncomputable def cocartesianTransportObject {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (e : B _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e)) _⦋0⦌ → (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 0 e)) _⦋0⦌ :=
  fun x ↦ (chooseCocartesianEdgeLift p e x).target

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "3.4.2.3" (partial := stronger-hyp) "仮定：単体集合の写像 p が余デカルトファイブレーション（Lean は HA の単位を持つ operadic fibration より強く、全ての底の辺で持ち上げがある場合に限る）。結論：指定の始点から底の辺への余デカルト持ち上げがある（semi-inert 辺に適用した結論は一致）。単位から semi-inert 辺だけの持ち上げを構成する部分は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.nonempty_cocartesianEdgeLift
