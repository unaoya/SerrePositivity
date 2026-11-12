module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedEvaluation

/-!
# 正規化された標準単体への持ち上げ

概要：負次数の Hom の元から、最上位成分とその微分だけを持つ成分族を作る。
方針：依存関数の一点支持を二つ加え、標準方程式と正の面の消滅を検証する。
規約：最上位成分は z、零番目の面は δz とし、他の成分は零とする。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化の評価の全射性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：指定した一つの成分だけに値を持つ成分族を作る。
方針：有限集合と次数の対を添字とする依存関数の一点支持を使う。
規約：次数の等式は添字の証明として保持する。
使われ方：HA 1.3.1.12 の正規化された単体の逆構成。 -/
def singleComponent {n : ℕ} (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n := Pi.single ⟨(J, k), hJ, hk⟩ z

/-- 概要：一点支持の成分族を支持点で評価すると指定値を得る。
方針：依存関数の一点支持の自己評価を使う。
規約：証明引数の選択に依存しない。
使われ方：HA 1.3.1.12 の最上位成分の回収。 -/
lemma singleComponent_self {n : ℕ} (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) (z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k) :
    (singleComponent J k hJ hk z).component J k hJ hk = z := by
  simp [singleComponent, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component]

/-- 概要：一点支持の成分族は異なる有限集合の成分で零である。
方針：有限集合が違えば依存関数の添字も違うことを使う。
規約：評価次数は任意の許される次数。
使われ方：HA 1.3.1.12 の支持外の方程式の検証。 -/
lemma singleComponent_other {n : ℕ} (J K : Finset (Fin (n + 1))) (k l : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hK : K.Nonempty) (hl : l = 1 - (K.card : ℤ)) (z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k) (h : K ≠ J) :
    (singleComponent J k hJ hk z).component K l hK hl = 0 := by
  apply Pi.single_eq_of_ne
  intro he
  exact h (congrArg (fun i ↦ i.val.1) he)

/-- 概要：最上位成分と零番目の面だけを持つ正次数の成分族を作る。
方針：全体集合に z、零番目の面に δz を一点支持で置く。
規約：両集合は正次数では異なり、ともに非空。
使われ方：HA 1.3.1.12 の正規化の逆写像の成分。 -/
def normalizedLiftData {n : ℕ} (z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (-(n + 1 : ℤ))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y (n + 1) :=
  singleComponent Finset.univ (-(n + 1 : ℤ)) Finset.univ_nonempty (by simp) z +
  singleComponent (Finset.univ.erase 0) (-(n + 1 : ℤ) + 1)
    (by apply Finset.card_pos.mp; simp) (by simp) (_root_.SerrePositivity.DifferentialGraded.differential R z)

private lemma component_add {m : ℕ} (f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y m)
    (J : Finset (Fin (m + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (f + g).component J k hJ hk = f.component J k hJ hk + g.component J k hJ hk := rfl

/-- 概要：二成分の持ち上げの最上位成分は元の値である。
方針：全体集合での一点支持を評価し、零番目の面の支持を除外する。
規約：正の chain 次数を n+1 とする。
使われ方：HA 1.3.1.12 の評価と持ち上げの合成。 -/
lemma normalizedLiftData_top {n : ℕ} (z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (-(n + 1 : ℤ))) :
    (normalizedLiftData z).component Finset.univ (-(n + 1 : ℤ))
      Finset.univ_nonempty (by simp) = z := by
  have h : (Finset.univ : Finset (Fin (n + 2))) ≠ Finset.univ.erase 0 := by
    intro he
    have := Finset.mem_univ (0 : Fin (n + 2))
    rw [he] at this
    simp at this
  rw [normalizedLiftData, component_add, singleComponent_self,
    singleComponent_other _ _ _ _ _ _ _ _ _ h, add_zero]

/-- 概要：二成分の持ち上げの零番目の面の成分は元の値の微分である。
方針：二つの一点支持を零番目の面で評価する。
規約：cochain 微分の次数は +1。
使われ方：HA 1.3.1.12 の標準方程式の検証。 -/
lemma normalizedLiftData_face {n : ℕ} (z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (-(n + 1 : ℤ))) :
    (normalizedLiftData z).component (Finset.univ.erase 0) (-(n + 1 : ℤ) + 1)
      (by apply Finset.card_pos.mp; simp) (by simp) = differential R z := by
  have h : (Finset.univ.erase 0 : Finset (Fin (n + 2))) ≠ Finset.univ := by
    intro he
    have : (0 : Fin (n + 2)) ∈ Finset.univ.erase 0 := by rw [he]; simp
    simp at this
  rw [normalizedLiftData, component_add, singleComponent_other _ _ _ _ _ _ _ _ _ h,
    singleComponent_self, zero_add]

/-- 概要：二成分の持ち上げは指定された二集合以外では零である。
方針：両方の一点支持の支持外評価を使う。
規約：次数は集合の濃度による通常の次数。
使われ方：HA 1.3.1.12 の残りの方程式と正の面の消滅。 -/
lemma normalizedLiftData_other {n : ℕ} (z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (-(n + 1 : ℤ)))
    (J : Finset (Fin (n + 2))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hfull : J ≠ Finset.univ) (hface : J ≠ Finset.univ.erase 0) :
    (normalizedLiftData z).component J k hJ hk = 0 := by
  rw [normalizedLiftData, component_add, singleComponent_other _ _ _ _ _ _ _ _ _ hfull,
    singleComponent_other _ _ _ _ _ _ _ _ _ hface, add_zero]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
