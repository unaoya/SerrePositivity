module

public import SerrePositivity.DifferentialGraded.Complexes.HomLimits

/-!
# 内部 Hom の前合成と鎖ホモトピー

概要：Berger–Moerdijk 命題 4.1 で始域の鎖ホモトピーを内部 Hom への前合成へ移す。
方針：次数 p の射に (-1)^p を掛けた前合成を次数 -1 のホモトピーとする。
規約：非有界複体の全整数次数を扱い、値域の cofibrancy を要求しない。
使われ方：区間の端点のホモトピー逆から定数射の擬同型性を導く。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.HomHomotopy

open _root_.CategoryTheory _root_.HomologicalComplex _root_.CochainComplex _root_.CochainComplex.HomComplex
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {X Y : Complex A}

/-- 概要：始域の次数 -1 の射を Hom 上の符号付き前合成へ移す（BM 命題 4.1）。
方針：次数 p の入力に (-1)^p を掛けて前合成する。
規約：微分との関係は後続のホモトピーの検証で確認する。
使われ方：内部 Hom 上の鎖ホモトピーの具体的な次数成分となる。 -/
def homPrecomposeHomotopyCochain (h : Homogeneous X Y (-1)) (B : Complex A) :
    Homogeneous (homComplex A Y B) (homComplex A X B) (-1) :=
  Cochain.mk (fun p q hpq => ModuleCat.ofHom {
    toFun := fun z => p.negOnePow • h.comp z (by omega)
    map_add' := by intro z z'; rw [Cochain.comp_add, smul_add]
    map_smul' := by
      intro a z
      simp only [RingHom.id_apply]
      rw [Cochain.comp_smul, smul_comm] })

private lemma homPrecomposeHomotopyCochain_boundary {f g : X ⟶ Y}
    (h : Homotopy f g) (B : Complex A) :
    δ (-1) 0 (_root_.SerrePositivity.HomHomotopy.homPrecomposeHomotopyCochain (Cochain.ofHomotopy h) B) =
      Cochain.ofHom (homPrecompose f B) - Cochain.ofHom (homPrecompose g B) := by
  apply Cochain.ext₀
  intro p
  rw [δ_v (-1) 0 (by omega) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
  simp only [Int.negOnePow_zero, one_smul]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change δ (p - 1) p (p.negOnePow • (Cochain.ofHomotopy h).comp z (by omega)) +
      (p + 1).negOnePow • (Cochain.ofHomotopy h).comp (δ p (p + 1) z) (by omega) =
    (Cochain.ofHom f).comp z (zero_add p) - (Cochain.ofHom g).comp z (zero_add p)
  rw [δ_units_smul, δ_comp _ z _ 0 (p + 1) p (by omega) (by omega) rfl]
  rw [δ_ofHomotopy]
  simp only [Cochain.sub_comp, Int.negOnePow_succ, Units.neg_smul, smul_add,
    smul_sub, smul_smul, Int.units_mul_self, one_smul]
  abel

/-- 概要：始域の鎖ホモトピーは内部 Hom の前合成の鎖ホモトピーを与える（BM 命題 4.1）。
方針：次数付き符号を含む前合成の微分を Leibniz 則で計算する。
規約：元のホモトピーと同じ向きで二つの前合成射を比較する。
使われ方：端点の鎖ホモトピー逆を内部 Hom の鎖ホモトピー逆へ移す。 -/
def homPrecomposeHomotopy {f g : X ⟶ Y} (h : Homotopy f g) (B : Complex A) :
    Homotopy (homPrecompose f B) (homPrecompose g B) :=
  (Cochain.equivHomotopy _ _).symm
    ⟨_root_.SerrePositivity.HomHomotopy.homPrecomposeHomotopyCochain (Cochain.ofHomotopy h) B,
      by rw [_root_.SerrePositivity.HomHomotopy.homPrecomposeHomotopyCochain_boundary, sub_add_cancel]⟩

/-- 概要：恒等射の前合成は Hom の恒等射（BM 命題 4.1）。
方針：閉構造の前合成の恒等則を明示的な Hom 射へ移す。
規約：任意の値域の複体を扱う。
使われ方：前合成のホモトピー同値の二つの三角形を閉じる。 -/
lemma homPrecompose_identity (X B : Complex A) :
    homPrecompose (𝟙 X) B = 𝟙 (homComplex A X B) := by
  rw [← complexHomWhiskerRight, eHomWhiskerRight_id]
  rfl

/-- 概要：始域の鎖ホモトピー同値は内部 Hom の逆向きの同値を与える（BM 命題 4.1）。
方針：前合成の合成則と二つのホモトピーを移送する。
規約：比較対象の順序は始域の同値と反対とする。
使われ方：余代数区間の端点の前合成を擬同型とする。 -/
def homPrecomposeHomotopyEquiv (e : HomotopyEquiv X Y) (B : Complex A) :
    HomotopyEquiv (homComplex A Y B) (homComplex A X B) where
  hom := homPrecompose e.hom B
  inv := homPrecompose e.inv B
  homotopyHomInvId :=
    (Homotopy.ofEq (homPrecompose_comp A e.inv e.hom B).symm).trans
      ((_root_.SerrePositivity.HomHomotopy.homPrecomposeHomotopy e.homotopyInvHomId B).trans
        (Homotopy.ofEq (_root_.SerrePositivity.HomHomotopy.homPrecompose_identity Y B)))
  homotopyInvHomId :=
    (Homotopy.ofEq (homPrecompose_comp A e.hom e.inv B).symm).trans
      ((_root_.SerrePositivity.HomHomotopy.homPrecomposeHomotopy e.homotopyHomInvId B).trans
        (Homotopy.ofEq (_root_.SerrePositivity.HomHomotopy.homPrecompose_identity X B)))

end SerrePositivity.HomHomotopy
