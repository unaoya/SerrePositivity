module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：通常の圏の始対象から、その nerve 全体への錐を直接作る。
方針：各合成可能射列に始対象からの一意な射を前置し、coslice の普遍性で束ねる。
規約：小圏の始対象は厳密な始対象であることを要求しない。
使われ方：Kerodon Corollary 4.7.3.22（Tag 02J5） の双対、HTT §4.1.1 の始対象の cofinality。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：単調写像の両端の順序集合に新しい始点を加える。
方針：零を零、後続元を元の写像の後続元に送る。
規約：新しい始点以外の相対順序は変えない。
使われ方：HTT §1.2.8、Kerodon §4.7.3（Tag 02H6） の錐の自然性。 -/
def prependOrderHom {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    Fin (m + 2) →o Fin (n + 2) where
  toFun := Fin.cases 0 (fun i ↦ (α i).succ)
  monotone' i j hij := by
    rcases i with ⟨_ | i, hi⟩
    · exact Fin.zero_le _
    rcases j with ⟨_ | j, hj⟩
    · have : i + 1 ≤ 0 := hij
      omega
    change (α ⟨i, by omega⟩).succ ≤ (α ⟨j, by omega⟩).succ
    apply (Fin.succ_le_succ_iff).2
    apply α.monotone
    change i ≤ j
    have : i + 1 ≤ j + 1 := hij
    omega

/-- 概要：始点を加えた単調写像は新しい始点を固定する。
方針：Fin.cases の零の分岐を計算する。
規約：両側の零は各有限順序集合の最初の元。
使われ方：HTT §1.2.8、Kerodon §4.7.3（Tag 02H6） の錐の端点。 -/
lemma prependOrderHom_zero {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    prependOrderHom α 0 = 0 := rfl

/-- 概要：始点を加えた単調写像は後続元上で元の写像の後続元になる。
方針：Fin.cases の後続元の分岐を計算する。
規約：右側の添字を一つずらす。
使われ方：HTT §1.2.8、Kerodon §4.7.3（Tag 02H6） の錐の自然性。 -/
lemma prependOrderHom_succ {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    prependOrderHom α i.succ = (α i).succ := rfl

/-- 概要：標準単体の射による補った単体への作用は順序写像表示の後合成。
方針：空次数は空写像、非空次数は表現可能単体の作用を計算する。
規約：r は頂点数。
使われ方：HTT §1.2.8、Kerodon §4.3.5（Tag 017V） の標準単体の join の自然性。 -/
lemma Join.stdAugEquiv_augHom {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (Δ[m] : SSet.{u}) r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (stdSimplex.map α) r a) =
      α.toOrderHom.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m r a) := by
  cases r with
  | zero => ext i; exact Fin.elim0 i
  | succ r => rfl

/-- 概要：点と単調写像の連結は、点を前置した写像との合成で計算できる。
方針：切断の左右に分け、左終域が一点であることを使う。
規約：左の終域の頂点数は 1。
使われ方：HTT §1.2.8、Kerodon §4.7.3（Tag 02H6） の標準単体の錐の自然性。 -/
lemma concat_prependOrderHom {m n r : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (ℓ : ℕ) (hℓ : ℓ ≤ r) (f : Fin ℓ →o Fin 1) (g : Fin (r - ℓ) →o Fin (m + 1))
    (i : Fin r) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f (α.comp g) i).val =
      (prependOrderHom α (Fin.cast (by omega) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f g i))).val := by
  by_cases hi : i.val < ℓ
  · have hf : f ⟨i.val, hi⟩ = 0 := Fin.ext (by have := (f ⟨i.val, hi⟩).isLt; omega)
    have he : Fin.cast (by omega) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f g i) = (0 : Fin (m + 2)) := Fin.ext (by
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f g i).val = 0
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ hi, hf]; rfl)
    rw [he, prependOrderHom_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ hi, hf]
    rfl
  · have hge : ℓ ≤ i.val := by omega
    let j : Fin (r - ℓ) := ⟨i.val - ℓ, by have := i.isLt; omega⟩
    have he : Fin.cast (by omega) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f g i) = (g j).succ := Fin.ext (by
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat ℓ hℓ f g i).val = (g j).val + 1
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ _ hge]
      change 1 + (g j).val = (g j).val + 1
      omega)
    rw [he, prependOrderHom_succ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ _ hge]
    change 1 + (α (g j)).val = (α (g j)).val + 1
    omega

/-- 概要：標準単体の次元の等式を標準単体の同型にする。
方針：単体圏の等式による同型を表現可能関手で写す。
規約：頂点の番号の自然数値を変えない。
使われ方：HTT §1.2.8 の点との join の次元の正規化。 -/
def simplexCastIso {m n : ℕ} (h : m = n) : (Δ[m] : SSet.{u}) ≅ Δ[n] :=
  stdSimplex.mapIso (eqToIso (congrArg SimplexCategory.mk h))

/-- 概要：次元の等式による標準単体の同型は各頂点の値を変えない。
方針：等式で置換して恒等写像に帰着する。
規約：次数 d の頂点添字 i は共通。
使われ方：HTT §1.2.8 の次元の正規化の自然性。 -/
lemma simplexCastIso_hom_app_val {m n : ℕ} (h : m = n) (d : ℕ)
    (s : (Δ[m] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    ((simplexCastIso h).hom.app (Opposite.op ⦋d⦌) s i).val = (s i).val := by
  subst n
  rfl

/-- 概要：点と標準単体の join を次元 n+1 の標準単体に同定する。
方針：既存の同型の 0+n+1 を次元の等式で正規化する。
規約：直接構成した join の表示は維持する。
使われ方：HTT §1.2.8、Kerodon §4.7.3（Tag 02H6） の始対象の錐。 -/
@[kerodon 0177]
def pointJoinStdSimplexIso (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[n] ≅ Δ[n + 1] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 n ≪≫ simplexCastIso (by omega)

/-- 概要：点との join の同型は連結した順序写像で評価できる。
方針：次元の正規化が頂点の値を変えないことを使う。
規約：次数 d とその頂点 i を明示する。
使われ方：HTT §1.2.8、Kerodon §4.7.3（Tag 02H6） の錐の自然性。 -/
lemma pointJoinStdSimplexIso_hom_app_val (n d : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) Δ[n] d) (i : Fin (d + 1)) :
    ((pointJoinStdSimplexIso n).hom.app (Opposite.op ⦋d⦌) s i).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode 0 n d s i).val :=
  simplexCastIso_hom_app_val (by omega) d ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 n).hom.app _ s) i

/-- 概要：点と標準単体の join の同型は右因子の標準単体の射に自然。
方針：連結写像と始点の前置の可換性を単体ごとに使う。
規約：次数の 0+n の括弧は標準単体の join の規約を保つ。
使われ方：HTT §1.2.8、Kerodon §4.7.3（Tag 02H6） の始対象の錐の自然性。 -/
lemma joinStdSimplexIso_point_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.map α) ≫ (pointJoinStdSimplexIso n).hom =
      (pointJoinStdSimplexIso m).hom ≫ stdSimplex.map
        (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change ((pointJoinStdSimplexIso n).hom.app (Opposite.op ⦋d⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.map α)).app (Opposite.op ⦋d⦌) s) i).val =
      (prependOrderHom α.toOrderHom
        ((pointJoinStdSimplexIso m).hom.app (Opposite.op ⦋d⦌) s i)).val
  rw [pointJoinStdSimplexIso_hom_app_val]
  have he : (pointJoinStdSimplexIso m).hom.app (Opposite.op ⦋d⦌) s i =
      Fin.cast (by omega) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode 0 m d s i) :=
    Fin.ext (pointJoinStdSimplexIso_hom_app_val _ _ _ _)
  rw [he]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat s.1.val (Nat.le_of_lt_succ s.1.isLt)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 0 _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (𝟙 Δ[0]) _ s.2.1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (stdSimplex.map α) _ s.2.2)) i).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id, Join.stdAugEquiv_augHom]
  exact concat_prependOrderHom α.toOrderHom _ _ _ _ i

/-- 概要：圏の対象を nerve の零単体として表す。
方針：長さ零の合成可能射列を使う。
規約：対象の宇宙 v と射の宇宙 w は独立で、nerve は SSet.{max v w}。
使われ方：HTT §4.1.1 の始対象の頂点包含。 -/
def nerveVertex {I : Type v} [Category.{w} I] (c : I) : (nerve I) _⦋0⦌ :=
  ComposableArrows.mk₀ c

/-- 概要：圏の対象に対応する nerve への頂点包含。
方針：零単体の Yoneda 表示を使う。
規約：始域は Δ[0]。
使われ方：HTT §4.1.1、Kerodon §7.2.2（Tag 02NQ） の始対象への制限。 -/
def nervePoint {I : Type v} [Category.{w} I] (c : I) : (Δ[0] : SSet.{max v w}) ⟶ nerve I :=
  SSet.yonedaEquiv.symm (nerveVertex c)

/-- 概要：始対象からの一意な射を合成可能射列に前置する。
方針：Mathlib の ComposableArrows.precomp を使う。
規約：新しい最初の対象は c、残りは元の射列。
使われ方：HTT §4.1.1、Kerodon Corollary 4.7.3.22（Tag 02J5） の双対の錐。 -/
noncomputable def initialChain {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {n : ℕ} (F : ComposableArrows I n) : ComposableArrows I (n + 1) :=
  F.precomp (hc.to F.left)

/-- 概要：始対象を前置した射列は添字の単調写像に自然。
方針：先頭の対象と残りの射列を比較し、先頭からの射は始対象性で一意にする。
規約：新しい始点を固定する prependOrderHom を使う。
使われ方：HTT §4.1.1、Kerodon §4.7.3（Tag 02H6） の始対象の錐の自然性。 -/
lemma initialChain_naturality {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (F : (nerve I) _⦋n⦌) :
    (nerve I).map (SimplexCategory.mkHom (prependOrderHom α.toOrderHom)).op (initialChain hc F) =
      initialChain hc ((nerve I).map α.op F) := by
  refine ComposableArrows.ext_succ ?_ ?_ ?_
  · rfl
  · rfl
  · exact hc.hom_ext _ _

/-- 概要：始対象を前置した射列の先頭の面を落とすと元の射列。
方針：ComposableArrows.precomp の定義を使う。
規約：先頭を落とす面は δ₀。
使われ方：HTT §4.1.1 の錐の元の図式への制限。 -/
lemma initialChain_tail {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {n : ℕ} (F : (nerve I) _⦋n⦌) : (nerve I).δ 0 (initialChain hc F) = F := rfl

/-- 概要：始対象を前置した射列の最初の頂点は c。
方針：長さ零の射列を先頭の対象で比較する。
規約：標準単体の零番目の頂点への制限。
使われ方：HTT §4.1.1 の錐の先端の固定。 -/
lemma initialChain_vertex {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {n : ℕ} (F : (nerve I) _⦋n⦌) :
    (nerve I).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (initialChain hc F) = nerveVertex c :=
  ComposableArrows.ext₀ rfl

/-- 概要：正規化した点との join の左包含は標準単体の最初の頂点。
方針：連結写像の左区間の値を計算する。
規約：標的の次元は n+1。
使われ方：HTT §4.1.1 の始対象の錐の先端の固定。 -/
lemma pointJoinStdSimplexIso_inl_vertex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[n] ≫ (pointJoinStdSimplexIso n).hom =
      SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2))) := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply stdSimplex.ext
  intro i
  fin_cases i
  apply Fin.ext
  change (((pointJoinStdSimplexIso n).hom.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) 0)).val = 0
  rw [pointJoinStdSimplexIso_hom_app_val]
  rfl

/-- 概要：正規化した点との join の右包含は標準単体の最初の面。
方針：連結写像の右区間で全ての頂点を一つずらす計算を使う。
規約：元の標準単体は δ₀ の面。
使われ方：HTT §4.1.1 の始対象の錐の図式への制限。 -/
lemma pointJoinStdSimplexIso_inr (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[n] ≫ (pointJoinStdSimplexIso n).hom = stdSimplex.δ 0 := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change (((pointJoinStdSimplexIso n).hom.app (Opposite.op ⦋n⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inr (SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u})))) i)).val =
      ((SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom i).val
  rw [pointJoinStdSimplexIso_hom_app_val]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat 0 (by omega) _ _ i).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ _ (by omega)]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inr, Nat.sub_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv]
  change 1 + i.val = ((0 : Fin (n + 2)).succAbove i).val
  rw [Fin.succAbove_zero]
  change 1 + i.val = i.val + 1
  omega

/-- 概要：始対象を前置した射列は、その対象からの錐を表す coslice の単体。
方針：点と標準単体の join の同型で前置した射列を錐に直す。
規約：先端は nervePoint c に固定する。
使われ方：HTT §4.1.1、Kerodon §4.7.3（Tag 02H6） の始対象からの錐。 -/
noncomputable def nerveInitialConeSimplex {I : Type v} [Category.{w} I] {c : I}
    (hc : IsInitial c) {n : ℕ} (F : (nerve I) _⦋n⦌) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (nervePoint c)) _⦋n⦌ :=
  ⟨(pointJoinStdSimplexIso n).hom ≫ (SSet.yonedaEquiv (X := nerve I)).symm (initialChain hc F), by
    rw [← Category.assoc, pointJoinStdSimplexIso_inl_vertex]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change (nerve I).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (initialChain hc F) = _
    exact initialChain_vertex hc F⟩

/-- 概要：始対象からの一意な射は nerve の全単体上で自然な錐を作る。
方針：前置した射列の自然性と点との join の同型の自然性を組み合わせる。
規約：標的は c 下の coslice。
使われ方：HTT §4.1.1、Kerodon Corollary 4.7.3.22（Tag 02J5） の双対の錐の束ね。 -/
noncomputable def nerveInitialSection {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    nerve I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (nervePoint c) where
  app _ := ↾fun F ↦ nerveInitialConeSimplex hc F
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    change (pointJoinStdSimplexIso n.unop.len).hom ≫
        (SSet.yonedaEquiv (X := nerve I)).symm (initialChain hc ((nerve I).map α F)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.map α.unop) ≫
        ((pointJoinStdSimplexIso m.unop.len).hom ≫
          (SSet.yonedaEquiv (X := nerve I)).symm (initialChain hc F))
    rw [← Category.assoc, joinStdSimplexIso_point_naturality, Category.assoc,
      SSet.yonedaEquiv_symm_naturality_left, initialChain_naturality]
    rfl

/-- 概要：始対象からの錐を射影すると元の nerve の単体に戻る。
方針：点との join の右包含は δ₀、前置した射列の δ₀ は元の射列である。
規約：射影との合成は恒等射。
使われ方：HTT §4.1.1 の始対象の錐の retract。 -/
lemma nerveInitialSection_projection {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    nerveInitialSection hc ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (nervePoint c) = 𝟙 (nerve I) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{max v w}) Δ[n] ≫
    ((pointJoinStdSimplexIso n).hom ≫
      (SSet.yonedaEquiv (X := nerve I)).symm (initialChain hc F))) = F
  rw [← Category.assoc, pointJoinStdSimplexIso_inr,
    stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, initialChain_tail]

/-- 概要：始対象から nerve 全体への錐を join からの射として束ねる。
方針：直接構成した coslice の普遍性で自然な錐を uncurry する。
規約：左因子が点、右因子が nerve。
使われ方：HTT §4.1.1、Kerodon Corollary 4.7.3.22（Tag 02J5） の双対の retract。 -/
noncomputable def nerveInitialCone {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{max v w}) (nerve I) ⟶ nerve I :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (nerveInitialSection hc)

/-- 概要：始対象からの錐は nerve 上で恒等。
方針：uncurry の射影の式と section の射影の恒等式を使う。
規約：右包含による制限。
使われ方：HTT §4.1.1 の頂点包含への retract の標的の逆関係。 -/
lemma nerveInitialCone_inr {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{max v w}) (nerve I) ≫ nerveInitialCone hc = 𝟙 (nerve I) := by
  rw [nerveInitialCone, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection, nerveInitialSection_projection]

/-- 概要：始対象 c の零射列に c を前置すると恒等辺になる。
方針：唯一の c→c の射が恒等射であることを使う。
規約：辺は零単体の σ₀ の退化。
使われ方：HTT §4.1.1 の始対象の錐の c 上の固定。 -/
lemma initialChain_self {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    initialChain hc (nerveVertex c) = (nerve I).σ 0 (nerveVertex c) := by
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · exact hc.hom_ext _ _

/-- 概要：始対象からの section は c の頂点で恒等錐を取る。
方針：前置された c→c が恒等辺であることと定数射の式を使う。
規約：coslice の恒等錐を Yoneda で零単体からの射にする。
使われ方：HTT §4.1.1、Kerodon Corollary 4.7.3.22（Tag 02J5） の retract の先端。 -/
lemma nerveInitialSection_at_point {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    nervePoint c ≫ nerveInitialSection hc =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (nervePoint c))).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone (nerveVertex c)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  apply Subtype.ext
  change (pointJoinStdSimplexIso 0).hom ≫
    (SSet.yonedaEquiv (X := nerve I)).symm (initialChain hc (nerveVertex c)) =
      SSet.const (nerveVertex c)
  rw [initialChain_self, ← stdSimplex.σ_comp_yonedaEquiv_symm]
  simp only [SSet.yonedaEquiv_symm_zero, SSet.comp_const]

/-- 概要：始対象からの錐を c 自身に制限すると c の恒等辺になる。
方針：section の c 上の値を uncurry する。
規約：join の両因子とも点になる制限。
使われ方：HTT §4.1.1、Kerodon Corollary 4.7.3.22（Tag 02J5） の矢の retract。 -/
lemma nerveInitialCone_at_point {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{max v w})) (nervePoint c) ≫ nerveInitialCone hc =
      SSet.const (nerveVertex c) := by
  rw [nerveInitialCone, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, nerveInitialSection_at_point,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
  rfl

/-- 概要：nerve の頂点包含は単射。
方針：標準零単体は各次数で一点なので、各成分が単射である。
規約：対象 c に始対象性は要求しない。
使われ方：HTT §4.1.1 の頂点包含への join の left anodyne 性の適用。 -/
instance nervePoint_mono {I : Type v} [Category.{w} I] (c : I) : Mono (nervePoint c) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro a b _
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  have ha := (a i).isLt
  have hb := (b i).isLt
  omega

/-- 概要：始対象の頂点包含は、その点を左から join した包含の矢の retract。
方針：元の nerve への右包含と始対象からの錐を使い、点側は元の点の端点を選ぶ。
規約：c に入る非恒等射の不存在は仮定しない。
使われ方：HTT §4.1.1、Kerodon Corollary 4.7.3.22（Tag 02J5） の双対。 -/
noncomputable def nervePointRetract {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    RetractArrow (nervePoint c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{max v w})) (nervePoint c)) where
  i := Arrow.homMk' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{max v w}) Δ[0])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{max v w}) (nerve I)) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap])
  r := Arrow.homMk' (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
    (nerveInitialCone hc) (by
      rw [nerveInitialCone_at_point, nervePoint, SSet.yonedaEquiv_symm_zero, SSet.comp_const])
  retract := by
    apply Arrow.hom_ext
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _
    · exact nerveInitialCone_inr hc

/-- 概要：通常の圏の始対象の nerve への頂点包含は left anodyne。
方針：単射を左から点と join した射の left anodyne 性を矢の retract で移す。
規約：任意の小圏と通常の始対象を扱い、有限性等は要求しない。
使われ方：HTT §4.1.1、Kerodon Corollary 4.7.3.22（Tag 02J5） の双対、§7.2.2。 -/
lemma nervePoint_leftAnodyne {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (nervePoint c) :=
  MorphismProperty.of_retract (nervePointRetract hc) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne.joinPoint_mono_leftAnodyne (nervePoint c))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
