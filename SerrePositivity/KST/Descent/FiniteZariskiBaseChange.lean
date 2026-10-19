module

public import SerrePositivity.KST.Descent.FiniteZariskiCover
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# 有限 Zariski 被覆族の実際の底変換

## 概要
有限型の圏内の有限開被覆族を任意の構造射へ実際に引き戻す。

## 方針
underlying scheme が指定引き戻しとなる有限型モデルを使い、点の持ち上げはスキームの引き戻しの点で構成する。

## 規約
元の有限添字を保持し、各 chart の rank の添字を変えない。

## 使われ方
論文 公理 (1)・(4)、補題 3.2 の同じ自然な transfer の全基底変更での局所検査。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

namespace FiniteTypeZariskiCover

variable {S : Scheme.{u}} [IsNoetherian S] {Y T : FiniteTypeSchemes S}
  (c : FiniteTypeZariskiCover Y) (q : T ⟶ Y)

/-- 概要：有限 Zariski 被覆族の任意の底変換（公理 (1)、補題 3.2）。
方針：指定 finiteTypePullback の第二射影と元の点の持ち上げを使う。
規約：元の有限添字を保持。使われ方：chart ごとの同じ rank による全基底変更の検査。 -/
def baseChange : FiniteTypeZariskiCover T where
  Index := c.Index
  finite := inferInstance
  obj i := finiteTypePullback (c.inclusion i) q
  inclusion i := finiteTypePullbackSnd (c.inclusion i) q
  openImmersion i := by
    change IsOpenImmersion (pullback.snd (c.inclusion i).hom.left q.hom.left)
    infer_instance
  covers t := by
    obtain ⟨i, x, hx⟩ := c.covers (q.hom.left t)
    obtain ⟨z, _hz, hz⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := (c.inclusion i).hom.left) (g := q.hom.left) x t hx
    exact ⟨i, z, hz⟩

/-- 概要：底変換した chart の構造射から元の chart への Over 内の指定射（補題 3.2）。
方針：元の第一射影と Cartesian 正方形の可換性を使う。
規約：Over の基底は元の Y に固定。使われ方：元の transfer の chart 上の rank 公式の制限。 -/
def baseChangeOverProjection (i : c.Index) :
    Over.mk ((c.baseChange q).inclusion i ≫ q) ⟶ Over.mk (c.inclusion i) :=
  Over.homMk (finiteTypePullbackFst (c.inclusion i) q)
    (finiteTypePullback_comm (c.inclusion i) q)

end FiniteTypeZariskiCover

end SerrePositivity.KST.Descent
