module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.SliceExtension
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：頂点の終対象・始対象の境界充填条件と trivial Kan fibration。
方針：端点を固定した正次元の境界充填を、join の境界の同型と slice の普遍性で比較する。
規約：終対象は最後の頂点、始対象は最初の頂点を固定する。
使われ方：HTT Definition 1.2.12.3、Kerodon Corollary 4.7.3.12（Tag 06R2）、極限の定義。

対応節は Kerodon 4.7（Tag 05EA）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet MorphismProperty
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 概要：trivial Kan fibration は全ての単射に対し右持ち上げ性を持つ射。
方針：単射のクラスの rlp として定義する。
規約：モデル構造や弱同値のクラスを使わない。
使われ方：Kerodon Definition 1.5.5.1（Tag 006W）、HTT §1.2.12 の slice 射影。 -/
@[kerodon 006W, kerodon 0075]
def trivialKanFibrations : MorphismProperty SSet.{u} := (monomorphisms SSet).rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange, IsStableUnderRetracts

/-- 概要：trivial Kan fibration への所属を型クラスとして表す。
方針：全単射に対する rlp への所属を保持する。
規約：充填の選択は構造に含めない。
使われ方：Kerodon Corollary 4.7.3.12（Tag 06R2） の終対象の特徴づけ。 -/
@[kerodon 006W]
class TrivialKanFibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop where
  mem : trivialKanFibrations p

/-- 概要：trivial Kan fibration 性は全境界包含に対する持ち上げ性と同値。
方針：単射の境界によるセル分解を使う。
規約：零次元の境界も含める。
使われ方：Kerodon Definition 1.5.5.1（Tag 006W）、Corollary 4.7.3.12（Tag 06R2） の境界テスト。 -/
@[kerodon 006W, kerodon 006Y]
lemma trivialKanFibration_iff_boundary {X Y : SSet.{u}} (p : X ⟶ Y) :
    TrivialKanFibration p ↔ ∀ n : ℕ, HasLiftingProperty (boundary n).ι p := by
  constructor
  · intro h n
    exact h.mem _ inferInstance
  · intro h
    constructor
    change (monomorphisms SSet.{u}).rlp p
    rw [SSet.rlp_monomorphisms]
    intro A B f hf
    cases hf with
    | mk n => exact h n

/-- 概要：trivial Kan fibration は右ファイブレーション。
方針：右ホーン包含は単射である。
規約：quasicategory 性を仮定しない。
使われ方：Kerodon §1.5.5（Tag 006V）、§4.7.3（Tag 02H6） の射影の性質。 -/
instance trivialKanFibration_rightFibration {X Y : SSet.{u}} (p : X ⟶ Y)
    [TrivialKanFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p where
  mem := by
    intro A B f hf
    cases hf with
    | intro i h0 => exact TrivialKanFibration.mem _ inferInstance

/-- 概要：trivial Kan fibration は左ファイブレーション。
方針：左ホーン包含は単射である。
規約：quasicategory 性を仮定しない。
使われ方：Kerodon §1.5.5（Tag 006V）、§4.7.3（Tag 02H6） の射影の性質。 -/
instance trivialKanFibration_leftFibration {X Y : SSet.{u}} (p : X ⟶ Y)
    [TrivialKanFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p where
  mem := by
    intro A B f hf
    cases hf with
    | intro i hn => exact TrivialKanFibration.mem _ inferInstance

/-- 概要：終対象となる頂点は、最後の頂点をそれに固定した全正次元境界を充填できる頂点。
方針：HTT の境界充填条件をそのまま Prop とする。
規約：n は一つ小さい次元で、境界は ∂Δ[n+1]、端点は n+1。
使われ方：HTT Definition 1.2.12.3、Kerodon Proposition 4.7.3.11（Tag 06R1） の終対象。 -/
@[kerodon 02H7, kerodon 06R1]
def IsTerminalVertex {X : SSet.{u}} (x : X _⦋0⦌) : Prop :=
  ∀ (n : ℕ) (b : (boundary (n + 1) : SSet.{u}) ⟶ X),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b = SSet.yonedaEquiv.symm x →
      ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (boundary (n + 1)).ι ≫ F = b

/-- 概要：終対象の境界充填条件は、点を右端に固定した join の全境界に対する延長性と同値。
方針：∂Δ[n]⋆Δ[0] と Δ[n] の和を ∂Δ[n+1] に同定し、最後の頂点を比較する。
規約：quasicategory 性はこの同値の証明には不要。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12（Tag 06R2） の射影の特徴づけ。 -/
lemma isTerminalVertex_iff_sliceOverExtension {X : SSet.{u}} (x : X _⦋0⦌) :
    IsTerminalVertex x ↔ ∀ n : ℕ,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.SliceOverExtensionProperty (boundary n) (SSet.yonedaEquiv.symm x) := by
  constructor
  · intro h n
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.SliceOverExtensionProperty
    rw [← boundary_zero]
    intro T hT
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryJoinIso.{u} n 0
    have hlast : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ (e.inv ≫ T) =
        SSet.yonedaEquiv.symm x := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryJoinIso_inr_vertex, Category.assoc, Category.assoc]
      change _ ≫ _ ≫ e.hom ≫ e.inv ≫ T = _
      rw [Iso.hom_inv_id_assoc]
      exact hT
    obtain ⟨F, hF⟩ := h n (e.inv ≫ T) hlast
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ F, ?_⟩
    calc
      _ = e.hom ≫ ((boundary (n + 1)).ι ≫ F) := by
        simpa only [Category.assoc] using
          (congrArg (fun z ↦ z ≫ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryJoinIso_hom_ι.{u} n 0)).symm
      _ = e.hom ≫ (e.inv ≫ T) := by rw [hF]
      _ = T := Iso.hom_inv_id_assoc e T
  · intro h n b hb
    have hh := h n
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.SliceOverExtensionProperty at hh
    rw [← boundary_zero] at hh
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryJoinIso.{u} n 0
    have hT : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (boundary n : SSet.{u}) Δ[0] ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft (boundary n) (boundary 0) ≫ (e.hom ≫ b) = SSet.yonedaEquiv.symm x := by
      have he := congrArg (fun z ↦ z ≫ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryJoinIso_inr_vertex.{u} n)
      simp only [Category.assoc] at he
      exact he.trans hb
    obtain ⟨L, hL⟩ := hh (e.hom ≫ b) hT
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ L, ?_⟩
    apply (cancel_epi e.hom).1
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary n) (boundary 0)).ι ≫ L := by
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryJoinIso_hom_ι, Category.assoc, Iso.hom_inv_id_assoc]
      _ = e.hom ≫ b := hL

/-- 概要：頂点が終対象であることは、その頂点上の slice 射影が trivial Kan fibration であることと同値。
方針：境界充填を join の延長性に直し、slice 射影の全境界に対する持ち上げ性と比較する。
規約：追加のモデル構造を使わず、任意の単体集合について成り立つ。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12（Tag 06R2）。 -/
@[kerodon 06R2]
lemma isTerminalVertex_iff_trivialKanFibration {X : SSet.{u}} (x : X _⦋0⦌) :
    IsTerminalVertex x ↔ TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)) := by
  rw [isTerminalVertex_iff_sliceOverExtension, trivialKanFibration_iff_boundary]
  constructor
  · intro h n
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverProjection_lifting_of_extension _ _ (h n)
  · intro h n
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverExtensionProperty_of_lifting _ _ (h n)

/-- 概要：始対象となる頂点は、最初の頂点をそれに固定した全正次元境界を充填できる頂点。
方針：終対象の境界充填条件の左右双対をそのまま Prop とする。
規約：境界は ∂Δ[n+1]、端点は 0。
使われ方：HTT Definition 1.2.12.3 の双対、Kerodon Proposition 4.7.3.11（Tag 06R1）。 -/
def IsInitialVertex {X : SSet.{u}} (x : X _⦋0⦌) : Prop :=
  ∀ (n : ℕ) (b : (boundary (n + 1) : SSet.{u}) ⟶ X),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm x →
      ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (boundary (n + 1)).ι ≫ F = b

/-- 概要：始対象の境界充填条件は、点を左端に固定した join の全境界に対する延長性と同値。
方針：Δ[0]⋆∂Δ[n] と Δ[n] の和を ∂Δ[n+1] に同定し、最初の頂点を比較する。
規約：quasicategory 性はこの同値の証明には不要。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12（Tag 06R2） の双対。 -/
lemma isInitialVertex_iff_sliceUnderExtension {X : SSet.{u}} (x : X _⦋0⦌) :
    IsInitialVertex x ↔ ∀ n : ℕ,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.SliceUnderExtensionProperty (boundary n) (SSet.yonedaEquiv.symm x) := by
  constructor
  · intro h n
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.SliceUnderExtensionProperty
    rw [← boundary_zero]
    intro T hT
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryJoinIso.{u} 0 n
    have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex (0 + n) 0 ≫ (e.inv ≫ T) = SSet.yonedaEquiv.symm x := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryJoinIso_inl_vertex, Category.assoc, Category.assoc]
      change _ ≫ _ ≫ e.hom ≫ e.inv ≫ T = _
      rw [Iso.hom_inv_id_assoc]
      exact hT
    obtain ⟨F, hF⟩ := h (0 + n) (e.inv ≫ T) hfirst
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 n).hom ≫ F, ?_⟩
    calc
      _ = e.hom ≫ ((boundary (0 + n + 1)).ι ≫ F) := by
        simpa only [Category.assoc] using
          (congrArg (fun z ↦ z ≫ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryJoinIso_hom_ι.{u} 0 n)).symm
      _ = e.hom ≫ (e.inv ≫ T) := by rw [hF]
      _ = T := Iso.hom_inv_id_assoc e T
  · intro h n
    have hn : ∀ b : (boundary (0 + n + 1) : SSet.{u}) ⟶ X,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex (0 + n) 0 ≫ b = SSet.yonedaEquiv.symm x →
          ∃ F : (Δ[0 + n + 1] : SSet.{u}) ⟶ X, (boundary (0 + n + 1)).ι ≫ F = b := by
      intro b hb
      have hh := h n
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.SliceUnderExtensionProperty at hh
      rw [← boundary_zero] at hh
      let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryJoinIso.{u} 0 n
      have hT : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (boundary n : SSet.{u}) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (boundary 0) (boundary n) ≫ (e.hom ≫ b) = SSet.yonedaEquiv.symm x := by
        have he := congrArg (fun z ↦ z ≫ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryJoinIso_inl_vertex.{u} n)
        simp only [Category.assoc] at he
        exact he.trans hb
      obtain ⟨L, hL⟩ := hh (e.hom ≫ b) hT
      refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 n).inv ≫ L, ?_⟩
      apply (cancel_epi e.hom).1
      calc
        _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (boundary 0) (boundary n)).ι ≫ L := by
          rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryJoinIso_hom_ι, Category.assoc, Iso.hom_inv_id_assoc]
        _ = e.hom ≫ b := hL
    rw [Nat.zero_add] at hn
    exact hn

/-- 概要：頂点が始対象であることは、その頂点下の coslice 射影が trivial Kan fibration であることと同値。
方針：境界充填を join の延長性に直し、coslice 射影の全境界に対する持ち上げ性と比較する。
規約：任意の単体集合に成り立ち、モデル構造は使わない。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12（Tag 06R2） の双対。 -/
@[kerodon 06R2]
lemma isInitialVertex_iff_trivialKanFibration {X : SSet.{u}} (x : X _⦋0⦌) :
    IsInitialVertex x ↔ TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) := by
  rw [isInitialVertex_iff_sliceUnderExtension, trivialKanFibration_iff_boundary]
  constructor
  · intro h n
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderProjection_lifting_of_extension _ _ (h n)
  · intro h n
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderExtensionProperty_of_lifting _ _ (h n)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.2.12.3"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration
attribute [cite HTT "1.2.12.6"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration
attribute [cite HTT "2.0.0.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary
attribute [cite HTT "2.0.0.5" (partial := component) "仮定：単体集合の射（HTT と一致）。結論：自明・Kan・左または右・内ファイブレーション間の含意の一部（Lean が弱い：(co)Cartesian と圏論的ファイブレーションまで含む図および逆向きの反例を揃えていない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_leftFibration
attribute [cite HTT "4.2.2.3" (partial := special) "仮定：指定の終端辺がデカルトなプリズムの持ち上げ問題（Lean が強い：q が自明 Kan ファイブレーションの場合）。結論：積と部分複体の包含による同じ単射に持ち上げ性を適用し、元の四角形の充填を得る（一致する場合。一般のデカルトファイブレーションは含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem
attribute [cite HTT "4.2.3.3" (partial := special) "仮定：準圏 C の単体 σ の初頂点が始対象（Lean が強い：σ が零単体の場合に適用）。結論：零単体の境界は空なので、同じコスライスの頂点射影が自明 Kan ファイブレーションとなる（その場合に一致。正次元の境界制限は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration
attribute [cite HTT "4.3.1.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
attribute [cite HTT "5.4.5.1" (partial := special) "仮定：accessible な C と終対象 x の一点図式（Lean が強い：任意の小図式 p ではなく終対象の一点）。結論：元の C/x は C への同じ射影が trivial Kan fibration、従って全準圏同値となるので accessible（この場合に一致）。同値模型を新しく仮定するのでなく終対象の既存判定から構成する。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration
attribute [cite HTT "5.4.5.15" (partial := special) "仮定：τ-accessible な C と τ-compact な始対象 x の一点図式（Lean が強い：一般の κ-small compact 図式を始対象の一点に限定）。結論：同じ Cx/ は C への射影が全準圏同値なので τ-accessible、かつ元の余錐の τ-compact 性は射影頂点の τ-compact 性と同値（この場合に両結論が一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration
attribute [cite HTT "5.4.5.16" (partial := special) "仮定：accessible な C と始対象 x の一点図式（Lean が強い）。結論：元の Cx/ の射影は終始対象の境界判定から trivial Kan fibration であり、C と全同値なので accessible（この場合に一致）。一般の小図式の下圏の生成性を結論したとは数えない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration
attribute [cite HTT "5.4.6.7" (partial := special) "仮定：accessible な C と終対象 x の一点図式（Lean が強い：p を終対象の一点に限定）。結論：同じ C/x は実際の射影によって C と全準圏同値、従って accessible（この場合に一致）。元の全 Hom と高次単体を保つ同値であり、通常圏の上圏への置換ではない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration
attribute [cite HTT "5.5.3.10" (partial := special) "仮定：presentable C と終対象 x の一点図式（Lean が強い：一般の小図式 p を終対象の一点に限定）。結論：同じ C/x の元の射影が全準圏同値であるため C/x は presentable（この場合に一致）。元の射影の同値は終対象の境界条件から構成でき、別の圏との未供給比較ではない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration
attribute [cite HTT "5.5.3.11" (partial := special) "仮定：presentable C と始対象 x の一点図式（Lean が強い：p を始対象の一点に限定）。結論：同じ Cx/ の元の射影が全準圏同値なので Cx/ は presentable（この場合に一致）。一般の小図式の下圏の compact 生成性は結論しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration
attribute [cite HTT "5.5.6.1" (partial := special) "仮定：準圏 C と整数 k≥−2（Lean が強い：k=−2 に限定）。結論：−2 切断対象を終対象とする明示された規約を、元の終対象述語で表す（この部分に一致）。全 k の写像空間のホモトピー群による切断性や全部分圏の族は定義していない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex
attribute [cite HTT "5.5.6.3" (partial := special) "仮定：準圏 C の対象と k≥−2（Lean が強い：k=−2 に限定）。結論：終対象 iff 最後の頂点を固定した全正次元境界の充填、という本文の n≥k+3 の条件そのもの（この場合に一致）。IsTerminalVertex の定義を展開すると両条件は同一で、一般の切断性は仮定しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex
