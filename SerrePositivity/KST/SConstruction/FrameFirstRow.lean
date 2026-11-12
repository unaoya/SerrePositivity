module
public import SerrePositivity.KST.SConstruction.ZeroFrameProjection

/-! # 枠の第一行の同定
概要：枠内の第一行を Fin n の nerve と厳密に同定する。
方針：正の右端と Fin n の succ・pred を対応させる。
規約：n=0 も含む。使われ方：零対角の射影と元の第一行制限の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：第一行の端点を枠の区間に送る。
方針：左端零の証明を付ける。
規約：順序を保つ。使われ方：枠内の第一行の同型。 -/
def firstRowFrameOrder (n : ℕ) : ULift.{u} (Fin n) →o FrameAr.{u} n where
  toFun j := ⟨firstRowOrder n j, Or.inl rfl⟩
  monotone' _ _ h := (firstRowOrder n).monotone h

/-- 概要：第一行 nerve を枠内の第一行へ写す。
方針：順序包含の nerve を全部分複体へ持ち上げる。
規約：対角は含めない。使われ方：第一行の二つの表示の比較。 -/
def firstRowFrameMap (n : ℕ) : firstRowNerve.{u} n ⟶ (framePositiveRow n : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (nerveMap (firstRowFrameOrder n).toFunctor) (by
    intro v
    constructor
    · rfl
    · change 0 < (nerveEquiv v).down.succ
      exact Nat.zero_lt_succ _)

/-- 概要：枠の第一行の鎖の各頂点は正の第一行にある。
方針：その頂点の定値な標準単体の射で条件を読む。
規約：次数は任意。使われ方：逆写像の pred の定義域。 -/
lemma frameRowChain_positive {n d : ℕ}
    (s : (framePositiveRow.{u} n : SSet.{u}) _⦋d⦌) (r : Fin (d + 1)) :
    IsPositiveRow (s.val.obj r).val := s.property (SimplexCategory.const ⦋0⦌ ⦋d⦌ r)

/-- 概要：枠の第一行の鎖から正の右端の直前を取り出す。
方針：各頂点の右端に pred を適用し、単調性を保つ。
規約：Fin n の鎖。使われ方：第一行同型の逆写像。 -/
def frameRowChainInverse {n d : ℕ}
    (s : (framePositiveRow.{u} n : SSet.{u}) _⦋d⦌) : ComposableArrows (ULift.{u} (Fin n)) d :=
  (show Monotone (fun r : Fin (d + 1) ↦ ULift.up
    ((s.val.obj r).val.down.val.2.pred (ne_of_gt (frameRowChain_positive s r).2))) from by
      intro r t h
      change ((s.val.obj r).val.down.val.2.val - 1) ≤
        ((s.val.obj t).val.down.val.2.val - 1)
      exact Nat.sub_le_sub_right (s.val.monotone h).2 1).functor

/-- 概要：枠内の第一行から Fin n の nerve への逆写像。
方針：鎖ごとの pred は引き戻しと厳密に可換。
規約：n=0 も同じ式。使われ方：第一行の同型。 -/
def frameFirstRowMap (n : ℕ) : (framePositiveRow n : SSet.{u}) ⟶ firstRowNerve n where
  app d := ↾fun s ↦ frameRowChainInverse s
  naturality {d e} α := rfl

/-- 概要：第一行の正の端点と Fin n は互いに逆。
方針：pred(succ j)=j を鎖の各頂点で使う。
規約：単体集合の厳密等号。使われ方：第一行同型の逆律。 -/
lemma firstRowFrameMap_comp (n : ℕ) : firstRowFrameMap.{u} n ≫ frameFirstRowMap n = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  apply ULift.ext
  change ((s.obj r).down.succ.pred (Fin.succ_ne_zero _)) = (s.obj r).down
  exact Fin.pred_succ _

/-- 概要：第一行の各枠の区間は右端と左端零から回復する。
方針：succ(pred j)=j と第一行の左端条件を使う。
規約：部分型の証明は proof irrelevance。使われ方：第一行同型の逆律。 -/
lemma frameFirstRowMap_comp (n : ℕ) : frameFirstRowMap.{u} n ≫ firstRowFrameMap n = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun r ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · exact (frameRowChain_positive s r).1.symm
  · change ((s.val.obj r).val.down.val.2.pred (ne_of_gt (frameRowChain_positive s r).2)).succ = (s.val.obj r).val.down.val.2
    exact Fin.succ_pred _ _

/-- 概要：枠内の第一行は Fin n の nerve と同型。
方針：succ と pred の互いに逆な鎖写像を組み合わせる。
規約：空の第一行も含む。使われ方：元の第一行制限と零対角補完の接続。 -/
def frameFirstRowIso (n : ℕ) : firstRowNerve.{u} n ≅ (framePositiveRow n : SSet.{u}) where
  hom := firstRowFrameMap n
  inv := frameFirstRowMap n
  hom_inv_id := firstRowFrameMap_comp n
  inv_hom_id := frameFirstRowMap_comp n

end SerrePositivity.KST.SConstruction
