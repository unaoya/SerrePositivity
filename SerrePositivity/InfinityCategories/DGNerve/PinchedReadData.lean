module
public import SerrePositivity.InfinityCategories.DGNerve.PinchedLinear
public import SerrePositivity.InfinityCategories.DGNerve.PinchedIndex

/-! # 端点の対象を固定したデータからの線形成分の回収

概要：先頭対象と最終対象が固定された任意の単体データから全終端成分を読む。
方針：最終点を加えた集合で hom を評価し、両端の対象を等式で移送する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：実際の単体と再構成データの共通の回収操作。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open CategoryTheory DifferentialGraded PinchedHom

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：固定した先頭対象と最終対象を持つデータから全ての線形成分を読む。
方針：J に最終点を加え、次数 1−|J| の成分を対象の等式で移送する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：順写像と逆構成のデータの往復。 -/
def toPinchedLinearData {n : ℕ} (s : SimplexData A D (n + 1)) (x y : D)
    (hx : ∀ i : Fin (n + 1), s.obj i.castSucc = x)
    (hy : s.obj (Fin.last (n + 1)) = y) : LinearData A x y n :=
  fun i => by
    let J := i.val.1
    let k := i.val.2
    have hJ : J.Nonempty := i.property.1
    have hk : k = 1 - (J.card : ℤ) := i.property.2
    let f := s.hom (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
      (two_withLast hJ) (min_withLast hJ _) (max_withLast J _) (by rw [card_withLast]; omega)
    exact cast (by rw [hx (J.min' hJ), hy]) f

/-- 概要：回収した成分は元の終端成分と異種等号で一致する。
方針：対象の等式で生じる cast を異種等号で除く。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：回収した成分の計算と逆則。 -/
lemma toPinchedLinearData_component_heq {n : ℕ} (s : SimplexData A D (n + 1)) (x y : D)
    (hx : ∀ i : Fin (n + 1), s.obj i.castSucc = x)
    (hy : s.obj (Fin.last (n + 1)) = y)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq ((s.toPinchedLinearData x y hx hy).component J k hJ hk)
      (s.hom (withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (two_withLast hJ) (min_withLast hJ _) (max_withLast J _)
        (by rw [card_withLast]; omega)) := cast_heq _ _

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
