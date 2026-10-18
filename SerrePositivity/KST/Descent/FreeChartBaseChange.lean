module

public import SerrePositivity.KST.Descent.FiniteTypeFreeCharts

/-!
# 実際の自由チャートの任意の底変換と基底の整合性

## 概要
選んだ正の有限基底を任意のアフィン底変換で保持し、実際の射影の Cartesian 性と rank を保つ。

## 方針
テンソル積の指定二射影の正方形を貼り、基底の底変換・自然性・反復の標準同型を検査する。

## 規約
各段で独立に基底や rank を選び直さない。係数底変換に追加の平坦性を要求しない。

## 使われ方
論文 補題 3.2 の transfer 自然変換と、Čech 各段で同じ局所 rank 公式を使うための入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
open scoped TensorProduct

namespace SerrePositivity.KST.Descent.FiniteFreeAffineChart

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : FiniteFreeAffineChart f)

/-- 概要：自由チャートの正の有限基底を任意のアフィン底変換へ移す（補題 3.2）。
方針：実際の有限基底の標準的な底変換を取る。
規約：同じ Fin rank を添字にする。新しい係数環の平坦性は不要。
使われ方：Čech 各段の実際の底変換代数の自明化。 -/
noncomputable def baseChangeBasis (S : Type u) [CommRing S] [Algebra c.baseRing S] :
    letI : Algebra c.baseRing c.sourceRing := c.algebra
    Basis (Fin c.rank) S (S ⊗[c.baseRing] c.sourceRing) := by
  let : Algebra c.baseRing c.sourceRing := c.algebra
  exact c.basis.baseChange S

/-- 概要：自由チャートの任意のアフィン底変換は元の射の実際の Cartesian モデル（補題 3.2）。
方針：テンソル積の指定射影の正方形を元の自由チャートの正方形に貼る。
規約：二つの構造射を保ち、対象の同型の存在だけに弱めない。
使われ方：実際の Čech 各段と transfer の底変換の指定射。 -/
theorem baseChange_isPullback (S : Type u) [CommRing S] [Algebra c.baseRing S] :
    letI : Algebra c.baseRing c.sourceRing := c.algebra
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        c.sourceRing →ₐ[c.baseRing] S ⊗[c.baseRing] c.sourceRing).toRingHom) ≫ c.sourceMap)
      (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[c.baseRing] c.sourceRing)))) f
      (Spec.map (CommRingCat.ofHom (algebraMap c.baseRing S)) ≫ c.baseMap) := by
  let : Algebra c.baseRing c.sourceRing := c.algebra
  exact (tensorSpecSquare_isPullback c.baseRing S c.sourceRing).flip.paste_horiz c.cartesian

/-- 概要：元の有限平坦射の rank は自由チャート上で基底の本数に一致（補題 3.2）。
方針：実際の Cartesian 正方形の rank 公式と基底の rank の一致を合成する。
規約：元の射の rank をチャートの代数の rank と無証明で同一視しない。
使われ方：元の被覆と局所 transfer の整数 rank の整合性。 -/
theorem rank_on_base [IsFinite f] [AlgebraicGeometry.Flat f] (y : Spec c.baseRing) :
    f.finrank (c.baseMap y) = c.rank := by
  let : Algebra c.baseRing c.sourceRing := c.algebra
  exact (Scheme.Hom.finrank_of_isPullback c.sourceMap
    (Spec.map (CommRingCat.ofHom (algebraMap c.baseRing c.sourceRing))) f c.baseMap
      c.cartesian y).symm.trans (c.rank_at_point y)

/-- 概要：任意のアフィン底変換の実際の射影も同じ定 rank（補題 3.2）。
方針：元の射への Cartesian 性とチャート上の rank を使う。
規約：新しい係数環の非零性や平坦性は仮定せず、各点で評価する。
使われ方：Čech の反復底変換で同じ正の rank を保持する。 -/
theorem baseChange_rank [IsFinite f] [AlgebraicGeometry.Flat f]
    (S : Type u) [CommRing S] [Algebra c.baseRing S] (s : Spec (.of S)) :
    letI : Algebra c.baseRing c.sourceRing := c.algebra
    (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[c.baseRing] c.sourceRing)))).finrank s =
      c.rank := by
  let : Algebra c.baseRing c.sourceRing := c.algebra
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ (c.baseChange_isPullback S) s).trans
    (c.rank_on_base ((Spec.map (CommRingCat.ofHom (algebraMap c.baseRing S))) s))

/-- 概要：選んだ基底の底変換はさらに係数写像に関して自然（論文 補題 3.2）。
方針：基底ベクトルが 1 ⊗ b_i であることとテンソル積写像の公式を使う。
規約：各係数環で独立に基底を選ばない。
使われ方：Čech の全ての面射・退化射で同じ自明化を使う。 -/
theorem baseChangeBasis_naturality {S T : Type u} [CommRing S] [CommRing T]
    [Algebra c.baseRing S] [Algebra c.baseRing T] (φ : S →ₐ[c.baseRing] T) (i : Fin c.rank) :
    letI : Algebra c.baseRing c.sourceRing := c.algebra
    (Algebra.TensorProduct.map φ (AlgHom.id c.baseRing c.sourceRing))
      (c.baseChangeBasis S i) = c.baseChangeBasis T i := by
  let : Algebra c.baseRing c.sourceRing := c.algebra
  simp [baseChangeBasis]

/-- 概要：基底の反復底変換は二重テンソル積の標準同型で直接の底変換基底に一致（補題 3.2）。
方針：基底ベクトルで検査し、テンソル積の結合・係数消去の公式を使う。
規約：同じ Fin rank を保持し、単なる非正準な基底の存在では済ませない。
使われ方：二重 Čech の両方向の底変換の自明化の整合性。 -/
theorem baseChangeBasis_iterated (S T : Type u) [CommRing S] [CommRing T]
    [Algebra c.baseRing S] [Algebra c.baseRing T] [Algebra S T]
    [IsScalarTower c.baseRing S T] :
    letI : Algebra c.baseRing c.sourceRing := c.algebra
    ((c.baseChangeBasis S).baseChange T).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange c.baseRing S T T c.sourceRing) =
        c.baseChangeBasis T := by
  let : Algebra c.baseRing c.sourceRing := c.algebra
  ext i
  simp [baseChangeBasis]

end SerrePositivity.KST.Descent.FiniteFreeAffineChart
