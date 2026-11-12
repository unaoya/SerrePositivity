module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra

/-! # 対象と次数の等式による斉次 Hom の移送

概要：端点と次数の等式に沿う斉次 Hom の線形同型は微分と合成を保つ。
方針：等式を消去し、恒等線形同型と既存の微分・合成へ帰着する。
規約：HA Construction 1.3.1.6。使われ方：境界から回収した残差を標準 fiber の Hom 座標へ移す。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：端点と次数の等式は斉次 Hom の線形同型を与える。
方針：三つの等式を消去して恒等線形同型を取る。
規約：HA Construction 1.3.1.6。使われ方：回収した cochain の対象と次数を固定する。 -/
def gradedHomTransport {x y x' y' : D} {k l : ℤ} (hx : x = x') (hy : y = y') (hk : k = l) :
    GradedHom A x y k ≃ₗ[A] GradedHom A x' y' l := by
  cases hx
  cases hy
  cases hk
  exact LinearEquiv.refl A _

/-- 概要：全ての等式が反射律なら斉次 Hom の移送は恒等。
方針：定義を評価する。
規約：HA Construction 1.3.1.6。使われ方：移送の反射的な場合の簡約。 -/
lemma gradedHomTransport_refl {x y : D} (k : ℤ) :
    gradedHomTransport (A := A) (rfl : x = x) (rfl : y = y) (rfl : k = k) =
      LinearEquiv.refl A _ := rfl

/-- 概要：等式に沿って移送した射は元の射と異種等号で一致する。
方針：端点と次数の等式を消去する。
規約：HA Construction 1.3.1.6。使われ方：回収した成分の異種等号を移送後の等号へ変える。 -/
lemma gradedHomTransport_heq {x y x' y' : D} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l) (f : GradedHom A x y k) :
    HEq (gradedHomTransport hx hy hk f) f := by
  cases hx
  cases hy
  cases hk
  rfl

/-- 概要：移送先の射との異種等号は移送後の通常の等号を与える。
方針：移送が元の射と異種等号で一致することと異種等号の推移性を使う。
規約：HA Construction 1.3.1.6。使われ方：標準 fiber の脚・高次成分を通常の cochain 等式へ移す。 -/
lemma gradedHomTransport_eq_of_heq {x y x' y' : D} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l) (f : GradedHom A x y k)
    (g : GradedHom A x' y' l) (hfg : HEq f g) :
    gradedHomTransport hx hy hk f = g :=
  eq_of_heq ((gradedHomTransport_heq hx hy hk f).trans hfg)

/-- 概要：斉次 Hom の移送は微分と可換。
方針：等式を消去し同じ微分の等式へ帰着する。
規約：HA Construction 1.3.1.6、微分は +1。使われ方：残差の微分恒等式を固定した対象へ移す。 -/
lemma gradedHomTransport_differential {x y x' y' : D} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l) (f : GradedHom A x y k) :
    gradedHomTransport hx hy (congrArg (fun q : ℤ => q + 1) hk) (differential A f) =
      differential A (gradedHomTransport hx hy hk f) := by
  cases hx
  cases hy
  cases hk
  rfl

/-- 概要：斉次 Hom の移送は通常順の合成を保つ。
方針：三対象と三次数の等式を消去し、次数の証明の一意性を使う。
規約：HA Construction 1.3.1.6。使われ方：脚・ホモトピーとの合成を標準 fiber の Hom 座標へ移す。 -/
lemma gradedHomTransport_compose {x y z x' y' z' : D} {p q k p' q' k' : ℤ}
    (hx : x = x') (hy : y = y') (hz : z = z') (hp : p = p') (hq : q = q') (hk : k = k')
    (g : GradedHom A y z q) (f : GradedHom A x y p) (h : p + q = k) :
    gradedHomTransport hx hz hk (compose A g f h) =
      compose A (gradedHomTransport hy hz hq g) (gradedHomTransport hx hy hp f)
        (by rw [← hp, ← hq, ← hk]; exact h) := by
  cases hx
  cases hy
  cases hz
  cases hp
  cases hq
  cases hk
  rfl

/-- 概要：移送の逆は逆向きの等式に沿う移送。
方針：全ての等式を消去する。
規約：HA Construction 1.3.1.6。使われ方：Hom 座標で求めた解を元の境界データへ戻す。 -/
lemma gradedHomTransport_symm {x y x' y' : D} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l) :
    (gradedHomTransport (A := A) hx hy hk).symm = gradedHomTransport hx.symm hy.symm hk.symm := by
  cases hx
  cases hy
  cases hk
  rfl

/-- 概要：二回の移送は合成した等式に沿う移送。
方針：全ての端点と次数の等式を消去する。
規約：HA Construction 1.3.1.6。使われ方：左右の共通成分の比較と標準対象への移送をまとめる。 -/
lemma gradedHomTransport_trans {x y x' y' x'' y'' : D} {k l m : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l)
    (hx' : x' = x'') (hy' : y' = y'') (hk' : l = m) :
    (gradedHomTransport (A := A) hx hy hk).trans (gradedHomTransport hx' hy' hk') =
      gradedHomTransport (hx.trans hx') (hy.trans hy') (hk.trans hk') := by
  cases hx
  cases hy
  cases hk
  cases hx'
  cases hy'
  cases hk'
  rfl

/-- 概要：異種等号で一致する二射を同じ端点・次数へ移送すると等しい。
方針：各移送と元の射との異種等号を共通の異種等号でつなぐ。
規約：HA Construction 1.3.1.6。使われ方：左右で異なる対象から回収した共通残差の比較。 -/
lemma gradedHomTransport_eq_of_heq_transport {x y x' y' z w : D} {k l m : ℤ}
    (hx : x = z) (hy : y = w) (hk : k = m)
    (hx' : x' = z) (hy' : y' = w) (hk' : l = m)
    (f : GradedHom A x y k) (g : GradedHom A x' y' l) (hfg : HEq f g) :
    gradedHomTransport hx hy hk f = gradedHomTransport hx' hy' hk' g :=
  eq_of_heq ((gradedHomTransport_heq hx hy hk f).trans
    (hfg.trans (gradedHomTransport_heq hx' hy' hk' g).symm))

/-- 概要：移送前の射との異種等号は移送後も異種等号として保たれる。
方針：移送と元の射との異種等号を合成する。
規約：HA Construction 1.3.1.6。使われ方：共通残差を一度だけ移送して右側の生データとも比較する。 -/
lemma gradedHomTransport_heq_of_heq {x y x' y' z w : D} {k l m : ℤ}
    (hx : x = z) (hy : y = w) (hk : k = m)
    (f : GradedHom A x y k) (g : GradedHom A x' y' l) (hfg : HEq f g) :
    HEq (gradedHomTransport hx hy hk f) g :=
  (gradedHomTransport_heq hx hy hk f).trans hfg

/-- 概要：閉じた斉次射の移送は閉じている。
方針：移送の微分との可換性と零の保存を使う。
規約：HA Construction 1.3.1.6。使われ方：回収した閉じた先頭右辺を Hom 座標へ移す。 -/
lemma gradedHomTransport_closed {x y x' y' : D} {k l : ℤ}
    (hx : x = x') (hy : y = y') (hk : k = l) (f : GradedHom A x y k)
    (hf : differential A f = 0) : differential A (gradedHomTransport hx hy hk f) = 0 := by
  rw [← gradedHomTransport_differential, hf, map_zero]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
