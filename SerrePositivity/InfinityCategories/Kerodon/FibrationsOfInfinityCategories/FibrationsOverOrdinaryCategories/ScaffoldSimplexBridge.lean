module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinRightBoundaryAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-!
概要：最初の辺と尾部の標準単体から全単体への inner anodyne な比較。
方針：最初の頂点の left anodyne な包含の右 join の相対境界を、辺と尾部の pushout へ移す。
規約：標準単体の次元は join の表示に合わせて 0+n+1 と書く。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、有限鎖上の scaffold の帰納段階。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：二頂点の join の右包含は標準区間の一端の包含に対応する。
方針：join の右頂点の式を Yoneda 同値で標準の面写像と比較する。
規約：一端の包含は δ₀。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、最初の辺と尾部を貼る頂点。 -/
lemma scaffoldIntervalCone_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom =
      stdSimplex.δ (0 : Fin 2) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso_inr_vertex 0]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply stdSimplex.ext
  intro i
  fin_cases i
  rfl

/-- 概要：標準区間の終点は二頂点の join の逆同型で右包含に戻る。
方針：順方向の包含の式を逆同型で打ち消す。
規約：順方向・逆方向とも既存の標準同型。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、最初の辺と尾部の pushout の条件。 -/
lemma scaffoldIntervalCone_endpoint :
    stdSimplex.δ (0 : Fin 2) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0] := by
  rw [← scaffoldIntervalCone_inr, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 概要：最初の辺と尾部を貼った対象から、尾部に新しい始点を加えた錐への射。
方針：辺を二頂点の join とし、尾部を右因子として貼る。
規約：共通の頂点は辺の終点と尾部の最初の頂点。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、最初の辺と尾部からの比較。 -/
noncomputable def scaffoldConeBridge (n : ℕ) :
    pushout (stdSimplex.δ (0 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex.{u} n) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[n] :=
  pushout.desc
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[n]) (by
      rw [← Category.assoc, scaffoldIntervalCone_endpoint, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap])

/-- 概要：錐への比較は最初の辺で指定した join の射を回収する。
方針：pushout の左包含の計算則を使う。
規約：左因子は標準区間。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、区間の係数部分の比較。 -/
lemma scaffoldConeBridge_inl (n : ℕ) :
    pushout.inl (stdSimplex.δ (0 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex.{u} n) ≫ scaffoldConeBridge n =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n) :=
  pushout.inl_desc _ _ _

/-- 概要：錐への比較は尾部で標準の右包含を回収する。
方針：pushout の右包含の計算則を使う。
規約：尾部は標準 n 単体。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、帰納仮定を使う尾部の比較。 -/
lemma scaffoldConeBridge_inr (n : ℕ) :
    pushout.inr (stdSimplex.δ (0 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex.{u} n) ≫ scaffoldConeBridge n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[n] := pushout.inr_desc _ _ _

/-- 概要：最初の辺と尾部から錐への比較は inner anodyne。
方針：右 join の相対境界の定理を最初の頂点に適用し、pushout の表示の同型で移す。
規約：n=0 の場合も含む。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、円柱から有限鎖の全体への拡張。 -/
lemma scaffoldConeBridge_innerAnodyne (n : ℕ) :
    innerAnodyneExtensions (scaffoldConeBridge.{u} n) := by
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex.{u} n
  have hp : IsPushout (stdSimplex.δ (0 : Fin 2)) i
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[0]) i)
      (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[0]) i) := by
    apply (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[0]) i).of_iso
      (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0) (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom, Category.id_comp] using scaffoldIntervalCone_inr.{u}
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  have he : scaffoldConeBridge n = hp.isoPushout.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap i Δ[0] := by
    apply pushout.hom_ext
    · rw [scaffoldConeBridge_inl, ← Category.assoc, hp.inl_isoPushout_inv,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap_join]
    · rw [scaffoldConeBridge_inr, ← Category.assoc, hp.inr_isoPushout_inv,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap_right]
  rw [he, innerAnodyneExtensions.cancel_left_of_respectsIso]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightBoundaryMap_innerAnodyne_of_leftAnodyne i Δ[0]
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex_leftAnodyne n)

/-- 概要：最初の辺と尾部を貼った対象から全標準単体への射。
方針：錐への比較に標準単体の join の同型を合成する。
規約：標的の次元は 0+n+1。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、有限鎖の全体へ写す比較。 -/
noncomputable def scaffoldSimplexBridge (n : ℕ) :
    pushout (stdSimplex.δ (0 : Fin 2)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex.{u} n) ⟶ Δ[0 + n + 1] :=
  scaffoldConeBridge n ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 n).hom

/-- 概要：最初の辺と尾部から全標準単体への比較は inner anodyne。
方針：錐への比較の inner anodyne 性を標的の同型で移す。
規約：標準同型の順方向を使う。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、有限鎖の全体比較の帰納段階。 -/
lemma scaffoldSimplexBridge_innerAnodyne (n : ℕ) :
    innerAnodyneExtensions (scaffoldSimplexBridge.{u} n) := by
  rw [scaffoldSimplexBridge, innerAnodyneExtensions.cancel_right_of_respectsIso]
  exact scaffoldConeBridge_innerAnodyne n

/-- 概要：最初の辺と尾部の比較は任意の係数との積を取っても inner anodyne。
方針：inner anodyne な射の直積による保存を使う。
規約：係数 K の Kan 性は要求しない。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、最初の係数値を付けた scaffold の拡張。 -/
lemma scaffoldSimplexBridge_whiskerRight_innerAnodyne (n : ℕ) (K : SSet.{u}) :
    innerAnodyneExtensions (scaffoldSimplexBridge n ▷ K) :=
  (scaffoldSimplexBridge_innerAnodyne n).whiskerRight K

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
