module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PushoutHomCoordinates

/-! # cofiber Hom 座標からの明示的な持ち上げ

概要：二つの脚側右辺と三角形側右辺の差から、標準 cofiber を始点とする未知成分を作る。
方針：三成分に共通の負一冪を掛けて座標同値の逆を使う。
規約：整合条件は微分の定理で明示する。使われ方：D7 の coslice 境界の明示解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {A B C X : Complex S}

/-- 概要：cofiber から出る未知成分を三つの右辺から明示的に作る。
方針：各座標に q.negOnePow を掛けて逆座標を適用する。
規約：第三引数は三角形側の右辺の差。使われ方：後続の未知成分。 -/
def pushoutHomBoundaryLift (f : A ⟶ B) (g : A ⟶ C) (q : ℤ)
    (a : Cochain B X (q + 1)) (b : Cochain C X (q + 1)) (c : Cochain A X q) :
    Cochain (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g) X (q + 1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates f g q).symm (q.negOnePow • c, (q.negOnePow • a, q.negOnePow • b))

/-- 概要：明示的な持ち上げの三座標は指定右辺の符号倍。
方針：座標同値の片側逆則を使う。
規約：共通符号は q.negOnePow。使われ方：脚とホモトピーとの合成の計算。 -/
lemma pushoutHomBoundaryLift_coordinates (f : A ⟶ B) (g : A ⟶ C) (q : ℤ)
    (a : Cochain B X (q + 1)) (b : Cochain C X (q + 1)) (c : Cochain A X q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates f g q (pushoutHomBoundaryLift f g q a b c) =
      (q.negOnePow • c, (q.negOnePow • a, q.negOnePow • b)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates f g q).apply_symm_apply _

/-- 概要：座標の微分条件を満たす持ち上げの微分は指定右辺に等しい。
方針：逆座標の微分公式と同値の逆則を使う。
規約：条件が実際の境界から従うことは別途証明する。使われ方：後続方程式の検証。 -/
lemma pushoutHomBoundaryLift_differential (f : A ⟶ B) (g : A ⟶ C) (q : ℤ)
    (a : Cochain B X (q + 1)) (b : Cochain C X (q + 1)) (c : Cochain A X q)
    (r : Cochain (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutCofiber f g) X (q + 1 + 1))
    (hR : (δ q (q + 1) (q.negOnePow • c) + (q + 1 + 1).negOnePow •
          ((Cochain.ofHom f).comp (q.negOnePow • a) (zero_add (q + 1)) -
            (Cochain.ofHom g).comp (q.negOnePow • b) (zero_add (q + 1))),
        (δ (q + 1) (q + 1 + 1) (q.negOnePow • a),
          δ (q + 1) (q + 1 + 1) (q.negOnePow • b))) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates f g (q + 1) r) :
    δ (q + 1) (q + 1 + 1) (pushoutHomBoundaryLift f g q a b c) = r := by
  rw [pushoutHomBoundaryLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutHomCoordinates_symm_differential,
    hR, LinearEquiv.symm_apply_apply]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
