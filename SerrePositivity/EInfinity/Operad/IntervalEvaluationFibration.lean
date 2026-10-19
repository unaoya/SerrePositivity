module

public import SerrePositivity.EInfinity.HomBiprodRestriction
public import SerrePositivity.EInfinity.Operad.ConvolutionPathAlgebra

/-!
# 区間の二端点評価の底の fibration 性

概要：Berger–Moerdijk 命題 4.1 の区間の二端点評価は底の複体で射影 fibration である。
方針：境界への前合成、両包含への制限、単位からの Hom の標準同型へ分解する。
規約：値域の代数・複体に cofibrancy を仮定しない。
使われ方：全代数の functorial path object と右転送の acyclicity に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad.CoalgebraInterval

open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {P : Operad A} {ε : P ⟶ commutativeOperad A}

/-- 概要：区間の二端点評価を底の複体の二項直和へ束ねる（BM 命題 4.1）。
方針：既存の始点評価と終点評価を二項直和への射にする。
規約：底の直和は複体の積でもある。
使われ方：全次数での全射性により評価の fibration 性を判定する。 -/
def evaluationPair (I : CoalgebraInterval ε) (B : Complex A) : I.pathComplex B ⟶ B ⊞ B :=
  biprod.lift (I.evaluation B false) (I.evaluation B true)

/-- 概要：二端点評価は境界制限と単位からの Hom の比較の合成（BM 命題 4.1）。
方針：両射影との合成を計算し、前合成の合成保存と境界の定義を使う。
規約：厳密な chain map の等式である。
使われ方：境界の cofibration 性から評価の全射性を導く。 -/
lemma evaluationPair_eq_boundary (I : CoalgebraInterval ε) (B : Complex A) :
    I.evaluationPair B = homPrecompose I.boundary B ≫
      homBiprodRestriction (𝟙_ (Complex A)) (𝟙_ (Complex A)) B ≫
      biprod.map (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom
        (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom := by
  apply biprod.hom_ext
  · simp only [evaluationPair, biprod.lift_fst, Category.assoc, biprod.map_fst,
      homBiprodRestriction, biprod.lift_fst_assoc, ← homPrecompose_comp_assoc,
      boundary, biprod.inl_desc, evaluation]
  · simp only [evaluationPair, biprod.lift_snd, Category.assoc, biprod.map_snd,
      homBiprodRestriction, biprod.lift_snd_assoc, ← homPrecompose_comp_assoc,
      boundary, biprod.inr_desc, evaluation]

/-- 概要：二端点評価は底の複体で射影 fibration（BM 命題 4.1）。
方針：境界制限の全次数全射性と、両包含への制限・比較同型の全射性を合成する。
規約：区間の境界の cofibration 条件だけを使い、値域は任意とする。
使われ方：転送モデル構造の path object の評価条件となる。 -/
lemma evaluationPair_projectiveFibration (I : CoalgebraInterval ε) (B : Complex A) :
    projectiveFibrations A (I.evaluationPair B) := by
  rw [evaluationPair_eq_boundary]
  intro n
  have he : IsIso ((biprod.map
      (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom
      (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom).f n) := by
    change IsIso (((HomologicalComplex.eval (ModuleCat A) (.up ℤ) n).mapIso
      (biprod.mapIso (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B))
        (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)))).hom)
    infer_instance
  have hs := (ModuleCat.epi_iff_surjective _).1 (inferInstance : Epi ((biprod.map
    (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom
    (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom).f n))
  exact hs.comp ((homBiprodRestriction_degreewise_surjective
    (𝟙_ (Complex A)) (𝟙_ (Complex A)) B n).comp
      (homPrecompose_projectiveFibration I.boundary I.boundary_cofibration B n))

/-- 概要：代数の自然な両端点評価の底の対は射影 fibration（BM 命題 4.1）。
方針：代数として構成した評価射の底を複体の評価へ厳密に同定する。
規約：転送先のモデル構造や代数の cofibrancy を仮定しない。
使われ方：代数の積を底の二項直和と比較した後で path object の評価条件にする。 -/
lemma algebraEvaluationPair_projectiveFibration (hP : Hopf P)
    (I : CoalgebraInterval hP.counit) (B : P.Algebra) :
    projectiveFibrations A (biprod.lift ((algebraEvaluationNat hP I false).app B).hom
      ((algebraEvaluationNat hP I true).app B).hom) := by
  rw [algebraEvaluationNat_hom, algebraEvaluationNat_hom]
  exact I.evaluationPair_projectiveFibration B.carrier

end SerrePositivity.EInfinity.Operad.CoalgebraInterval
