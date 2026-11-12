module
public import SerrePositivity.KST.SConstruction.ArCofiberInputs
public import SerrePositivity.KST.SConstruction.ZeroSpanProjection

/-! # 枠から取り出す cofiber の span
概要：各区間 (i,j) の二辺 (0,i)→(0,j) と (0,i)→(i,i) を枠の中で貼る。
方針：順序写像と、Ar[n] を掛けた span ホーンの pushout を使う。
規約：零射を含む入力全体を厳密に固定する。
使われ方：HTT 1.2.8 の関手単体集合を用いる相対 cofiber 補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：区間 (i,j) の始点から対角への辺を枠の中に取る。
方針：第一端点を 0 から i へ動かし、第二端点を i に保つ。
規約：j に依存せず自然。使われ方：cofiber の零射の入力。 -/
def arCofiberZeroInputOrder (n : ℕ) : Ar.{u} n × ULift.{u} (Fin 2) →o FrameAr.{u} n where
  toFun p := ⟨arObj (intervalStep 0 p.1.down.val.1 (Fin.zero_le _) p.2.down)
    p.1.down.val.1 (intervalStep_le _ _ _ _), by
      change (if p.2.down = 0 then 0 else p.1.down.val.1) = 0 ∨
        (if p.2.down = 0 then 0 else p.1.down.val.1) = p.1.down.val.1
      split <;> simp⟩
  monotone' a b h := by
    constructor
    · exact ((intervalStep 0 a.1.down.val.1 (Fin.zero_le _)).monotone h.2).trans
        (intervalStep_mono_endpoints _ _ le_rfl h.1.1 _)
    · exact h.1.1

/-- 概要：Ar[n] 上の対角へ向かう辺の自然な族を枠に写す。
方針：二つの鎖を頂点ごとに合わせる。
規約：Ar[n] が第一因子。使われ方：span の第二辺。 -/
def arCofiberZeroInputMap (n : ℕ) : arNerve.{u} n ⊗ Δ[1] ⟶ frameNerve n where
  app d := ↾fun s ↦ (show Monotone (fun r : Fin (d.unop.len + 1) ↦
    arCofiberZeroInputOrder n (s.1.obj r, ULift.up (stdSimplex.asOrderHom s.2 r))) from by
      intro r t h
      exact (arCofiberZeroInputOrder n).monotone
        ⟨s.1.monotone h, (stdSimplex.asOrderHom s.2).monotone h⟩).functor
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    rfl

/-- 概要：二つの入力辺の始点は枠の同じ頂点 (0,i)。
方針：鎖の各頂点で区間座標を零にする。
規約：全次数での厳密等号。使われ方：span の貼り合わせ。 -/
lemma arCofiberInputs_commonSource (n : ℕ) :
    (arNerve n ◁ stdSimplex.δ (1 : Fin 2)) ≫ arCofiberInputMap.{u} n =
      (arNerve n ◁ stdSimplex.δ (1 : Fin 2)) ≫ arCofiberZeroInputMap n := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  have hs : stdSimplex.asOrderHom s.2 r = 0 := Fin.eq_zero _
  have he : stdSimplex.asOrderHom ((stdSimplex.δ (1 : Fin 2)).app d s.2) r = 0 := by
    change (SimplexCategory.δ (1 : Fin 2)).toOrderHom (stdSimplex.asOrderHom s.2 r) = 0
    rw [hs]
    rfl
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · change 0 = intervalStep 0 _ _ (stdSimplex.asOrderHom ((stdSimplex.δ (1 : Fin 2)).app d s.2) r)
    rw [he]
    rfl
  · change intervalStep _ _ _ (stdSimplex.asOrderHom ((stdSimplex.δ (1 : Fin 2)).app d s.2) r) = _
    rw [he]
    rfl

/-- 概要：Ar[n] を掛けた span ホーンも二辺の pushout。
方針：閉モノイダル構造の左テンソルが colimit を保つことを使う。
規約：第一因子は Ar[n]。使われ方：枠内の入力 span の構成と一意性。 -/
lemma arCofiberSpan_isPushout (n : ℕ) :
    IsPushout (arNerve.{u} n ◁ stdSimplex.δ (1 : Fin 2))
      (arNerve n ◁ stdSimplex.δ (1 : Fin 2))
      (arNerve n ◁ horn₂₀.ι₀₁) (arNerve n ◁ horn₂₀.ι₀₂) :=
  horn₂₀.isPushout.map (tensorLeft (arNerve.{u} n))

/-- 概要：全区間の cofiber の span を枠だけから自然に取る。
方針：第一行の辺と対角への辺を共通の始点で貼る。
規約：入力の二辺を共に固定する。使われ方：零 span 上の cofiber 射影への入力。 -/
def arCofiberSpanMap (n : ℕ) : arNerve.{u} n ⊗ (horn 2 0 : SSet.{u}) ⟶ frameNerve n :=
  (arCofiberSpan_isPushout n).desc (arCofiberInputMap n)
    (arCofiberZeroInputMap n) (arCofiberInputs_commonSource n)

/-- 概要：貼り合わせた span の第一辺は第一行の入力。
方針：pushout の第一包含の式を使う。
規約：厳密等号。使われ方：枠の入力との照合。 -/
lemma arCofiberSpanMap_left (n : ℕ) :
    (arNerve n ◁ horn₂₀.ι₀₁) ≫ arCofiberSpanMap.{u} n = arCofiberInputMap n :=
  (arCofiberSpan_isPushout n).inl_desc _ _ _

/-- 概要：貼り合わせた span の第二辺は対角への入力。
方針：pushout の第二包含の式を使う。
規約：厳密等号。使われ方：零射の厳密な保存。 -/
lemma arCofiberSpanMap_right (n : ℕ) :
    (arNerve n ◁ horn₂₀.ι₀₂) ≫ arCofiberSpanMap.{u} n = arCofiberZeroInputMap n :=
  (arCofiberSpan_isPushout n).inr_desc _ _ _

/-- 概要：cofiber 四角形の左辺も枠内の対角への入力に等しい。
方針：横座標を零とした鎖の頂点を計算する。
規約：全次数での厳密等号。使われ方：自然な四角形と span の接続。 -/
lemma arCofiberSquareMap_left (n : ℕ) :
    (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge) ≫ arCofiberSquareMap.{u} n =
      arCofiberZeroInputMap n ≫ frameInclusion n := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  rfl

/-- 概要：自然な cofiber 四角形の入力 span は枠から抽出したものと一致。
方針：二辺へ制限し、pushout の一意性を使う。
規約：gapped 条件なしの形状の等号。使われ方：既存境界の相対補完との厳密な一致。 -/
lemma arCofiberSquareMap_span (n : ℕ) :
    (arNerve n ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary) ≫ arCofiberSquareMap.{u} n =
      arCofiberSpanMap n ≫ frameInclusion n := by
  apply (arCofiberSpan_isPushout n).hom_ext
  · simp only [← Category.assoc, ← whiskerLeft_comp]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge, arCofiberSquareMap_bottom,
      arCofiberSpanMap_left]
  · simp only [← Category.assoc, ← whiskerLeft_comp]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge, arCofiberSquareMap_left,
      arCofiberSpanMap_right]

end SerrePositivity.KST.SConstruction
