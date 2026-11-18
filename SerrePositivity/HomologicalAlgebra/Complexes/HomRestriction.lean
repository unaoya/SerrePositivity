module

public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveCofibration
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-!
# 内部 Hom の cofibration への制限

概要：Hovey §2.3、Berger–Moerdijk 命題 4.1 の区間評価の底の全射性を扱う。
方針：各次数での分裂を用い、任意の次数付き射の族を成分ごとに延長する。
規約：値域の複体の cofibrancy や有界性を要求しない。
使われ方：区間の境界の前合成が射影 fibration となることを示す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.HomRestriction

open _root_.CategoryTheory _root_.HomologicalComplex _root_.CochainComplex _root_.CochainComplex.HomComplex
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：各次数で分裂する包含への Hom の制限は各次数で全射（BM 命題 4.1）。
方針：次数付き射の族に分裂の射を前合成して延長する。
規約：分裂の微分との可換性は不要である。
使われ方：任意の値域への区間の境界制限を fibration と判定する。 -/
lemma homPrecompose_degreewise_surjective {X Y : Complex A} (f : X ⟶ Y)
    (hf : ∀ p : ℤ, IsSplitMono (f.f p)) (B : Complex A) (n : ℤ) :
    Function.Surjective ((homPrecompose f B).f n) := by
  let (p : ℤ) : IsSplitMono (f.f p) := hf p
  intro z
  let w : Homogeneous Y B n := Cochain.mk (fun p q hpq => retraction (f.f p) ≫ z.v p q hpq)
  refine ⟨w, ?_⟩
  rw [homPrecompose_apply]
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, w, Cochain.mk_v,
    IsSplitMono.id_assoc]

/-- 概要：射影 cofibration への内部 Hom の制限は射影 fibration（BM 命題 4.1）。
方針：左持ち上げ性から導いた次数ごとの分裂に成分の全射性を適用する。
規約：モデル構造の instance を仮定しない。
使われ方：全代数の path object の評価の底の fibration 性を供給する。 -/
lemma homPrecompose_projectiveFibration {X Y : Complex A} (f : X ⟶ Y)
    (hf : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp f) (B : Complex A) :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A (homPrecompose f B) :=
  _root_.SerrePositivity.HomRestriction.homPrecompose_degreewise_surjective f (_root_.SerrePositivity.ProjectiveCofibration.projectiveCofibration_degreewise_isSplitMono f hf) B

end SerrePositivity.HomRestriction
