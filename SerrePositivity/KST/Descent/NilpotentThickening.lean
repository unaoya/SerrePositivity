module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# 論文 §3 の冪零 thickening

## 概要
核イデアル層が冪零な閉埋め込みを定義し、台の上で全射であることを証明する。

## 方針
核イデアル層の正の冪の台は元の台に一致する。冪が零なら台はスキーム全体。
閉埋め込みの像が閉であることと組み合わせる。

## 規約
始域または終域の被約性だけで冪零性を置き換えない。
Noether 性や有限次元性はこの基本補題には不要。

## 使われ方
論文 補題 3.3・定理 3.1 の被約化と、公理 (3) の正確な幾何学的入力。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：核イデアル層が冪零な閉埋め込み（論文 §3、公理 (3)）。
方針：実際の閉埋め込みと、その核イデアル層の冪零性を保持する。
規約：位相空間の同相性だけを条件とする定義ではない。
使われ方：前層 L の冪零不変性と reduction の比較。 -/
class IsNilpotentThickening {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop
    extends IsClosedImmersion f where
  /-- 概要：閉埋め込みの核イデアル層が冪零（論文 §3）。
  方針：イデアル層の冪が零になることを要求する。
  規約：冪の指数は実際のスキーム上で存在する。
  使われ方：公理 (3) の適用条件。 -/
  nilpotent_ker : IsNilpotent f.ker

/-- 概要：冪零 thickening の核の台は終域全体（論文 補題 3.3）。
方針：零になる冪を一つ増やして正の冪とし、台の冪不変性を使う。
規約：空スキームの場合も含む。
使われ方：点全射性と、被約な終域に対する同型性。 -/
theorem nilpotentThickening_support_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNilpotentThickening f] : f.ker.support = ⊤ := by
  obtain ⟨n, hn⟩ := IsNilpotentThickening.nilpotent_ker (f := f)
  have hn' : f.ker ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  have h := congrArg Scheme.IdealSheafData.support hn'
  simpa only [Scheme.IdealSheafData.support_pow_succ,
    show (0 : Y.IdealSheafData) = ⊥ from rfl, Scheme.IdealSheafData.support_bot] using h

/-- 概要：冪零 thickening は点上全射（論文 補題 3.3・定理 3.1 の被約化）。
方針：核の台は像の閉包であり、閉埋め込みの像はすでに閉である。
規約：単に稠密な像から全射性を結論しない。
使われ方：被約な終域への全射閉埋め込みの同型性を適用する。 -/
theorem nilpotentThickening_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNilpotentThickening f] : Surjective f := by
  rw [surjective_iff, ← Set.range_eq_univ]
  have h := congrArg (fun Z : TopologicalSpace.Closeds Y ↦ (Z : Set Y))
    (nilpotentThickening_support_eq_top f)
  simpa only [Scheme.Hom.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq,
    TopologicalSpace.Closeds.coe_top] using h

/-- 概要：同型射は冪零 thickening（論文 §3、公理 (3) の恒等的な場合）。
方針：同型射の核イデアル層は零である。
規約：この事実だけで一般の冪零不変性を証明したとは扱わない。
使われ方：不変性の型と同型による幾何データの移し替え。 -/
instance isNilpotentThickening_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    IsNilpotentThickening f where
  nilpotent_ker := by
    rw [Scheme.Hom.ker_eq_bot_of_isIso]
    exact ⟨1, by simp only [pow_one]; rfl⟩

end SerrePositivity.KST.Descent
