module

public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveCofibrantUnit
public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveHomotopyInverse
public import SerrePositivity.HomologicalAlgebra.Complexes.HomHomotopy
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionPathAlgebra

/-!
模型。文献の定義との比較は後で
# 区間の定数射の底の擬同型性

概要：Berger–Moerdijk 命題 4.1 の余代数区間からの定数関数への射は底で擬同型となる。
方針：端点の trivial cofibration の鎖ホモトピー逆を Hom へ移し、定数と評価の三角形を使う。
規約：値域の cofibrancy と区間の鎖ホモトピー同値性を追加仮定にしない。
使われ方：全代数の functorial path object の弱同値条件となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} {ε : P ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A}

/-- 概要：区間の始点の前合成は任意の値域への Hom 複体で擬同型（BM 命題 4.1）。
方針：始点の cofibration と擬同型性から鎖ホモトピー逆を構成し、前合成へ移す。
規約：全ての非有界値域複体に適用する。
使われ方：端点評価と定数射の擬同型性を得る。 -/
lemma endpoint_false_precompose_quasiIso (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) (B : Complex A) :
    QuasiIso (homPrecompose (I.endpoint false) B) := by
  obtain ⟨e, he⟩ := _root_.SerrePositivity.ProjectiveHomotopyInverse.projectiveTrivialCofibration_homotopyEquiv (I.endpoint false)
    I.endpoint_false_cofibration (I.endpoint_quasiIso false)
  rw [← he]
  exact (_root_.SerrePositivity.HomHomotopy.homPrecomposeHomotopyEquiv e B).quasiIso_hom

/-- 概要：区間の始点評価は任意の値域について擬同型（BM 命題 4.1）。
方針：端点の前合成と標準の単位同型を合成する。
規約：代数構造や値域の cofibrancy を使わない。
使われ方：定数射と評価の三角形に擬同型の二対三性を適用する。 -/
lemma evaluation_false_quasiIso (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) (B : Complex A) :
    QuasiIso (I.evaluation B false) := by
  have := I.endpoint_false_precompose_quasiIso B
  change QuasiIso (homPrecompose (I.endpoint false) B ≫
    (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom)
  infer_instance

/-- 概要：区間上の定数関数への射は底の複体で擬同型（BM 命題 4.1）。
方針：始点評価との合成が恒等射であることと擬同型の二対三性を使う。
規約：余代数区間の指定した条件から導き、値域は任意とする。
使われ方：代数の path object の第一射の弱同値性を供給する。 -/
lemma constant_quasiIso (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) (B : Complex A) :
    QuasiIso (I.constant B) := by
  have := I.evaluation_false_quasiIso B
  have : QuasiIso (I.constant B ≫ I.evaluation B false) := by
    rw [I.constant_evaluation]
    infer_instance
  exact quasiIso_of_comp_right (I.constant B) (I.evaluation B false)

/-- 概要：区間の両端点での評価は底の複体で擬同型（BM 命題 4.1）。
方針：定数射と指定端点評価の三角形に二対三性を使う。
規約：始点の証明から終点も同じ定数射を用いて導く。
使われ方：path object の両評価の弱同値性を明示する。 -/
lemma evaluation_quasiIso (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) (B : Complex A) (b : Bool) :
    QuasiIso (I.evaluation B b) := by
  have := I.constant_quasiIso B
  have : QuasiIso (I.constant B ≫ I.evaluation B b) := by
    rw [I.constant_evaluation]
    infer_instance
  exact quasiIso_of_comp_left (I.constant B) (I.evaluation B b)

/-- 概要：自然な代数の定数射の底は擬同型（BM 命題 4.1）。
方針：代数の射の底と既存の複体の定数射の厳密な一致を使う。
規約：転送先のモデル構造や代数の cofibrancy を仮定しない。
使われ方：代数の path object の弱同値条件となる。 -/
lemma algebraConstantNat_quasiIso (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit)
    (B : P.Algebra) : QuasiIso ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraConstantNat hP I).app B).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraConstantNat_hom]
  exact I.constant_quasiIso B.carrier

/-- 概要：自然な代数の両端点評価の底は擬同型（BM 命題 4.1）。
方針：代数としての評価射の底と複体の評価を厳密に照合する。
規約：両端点と全ての値域代数に適用する。
使われ方：代数の path object の評価の弱同値性を示す。 -/
lemma algebraEvaluationNat_quasiIso (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit)
    (B : P.Algebra) (b : Bool) : QuasiIso ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationNat hP I b).app B).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationNat_hom]
  exact I.evaluation_quasiIso B.carrier b

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval
