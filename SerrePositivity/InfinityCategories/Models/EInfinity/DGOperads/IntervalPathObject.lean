module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraProducts
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraTerminal
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraModelClasses
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IntervalConstantQuasiIso
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IntervalEvaluationFibration

/-!
模型。文献の定義との比較は後で
# 余代数区間からの good path object

概要：Berger–Moerdijk 命題 4.1 の全代数の good path object を構成する。
方針：底の擬同型・評価の全射性を、直和上の積代数と選んだ積の比較で移す。
規約：モデル構造は仮定せず、忘却の逆像の二つの射の類を局所的に選ぶ。
使われ方：fibrations.llp の acyclicity を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：代数の二端点評価を底の直和上の積へ束ねる（BM 命題 4.1）。
方針：既存の二つの自然な評価代数射を積へ持ち上げる。
規約：底は既存の二端点評価の対に厳密に一致する。
使われ方：選んだ積への評価の fibration 性を検証する。 -/
def algebraEvaluationPair (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) (B : P.Algebra) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraPathFunctor hP I).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProduct B B :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductLift ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationNat hP I false).app B)
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationNat hP I true).app B)

/-- 概要：prepath object の評価は積の比較の後で二端点評価に等しい（BM 命題 4.1）。
方針：二つの射影後で比較する。
規約：等式は代数射の等式。
使われ方：評価の底の全射性を選んだ積へ移す。 -/
lemma prepathAlgebra_p_compare (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit)
    (B : P.Algebra) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.prepathAlgebra hP I B).p ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductIso B B).hom =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationPair hP I B := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProduct_hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductIso_hom_fst, PrepathObject.p_fst]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    exact (biprod.lift_fst _ _).symm
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductIso_hom_snd, PrepathObject.p_snd]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    exact (biprod.lift_snd _ _).symm

/-- 概要：選んだ代数の積への prepath 評価は底で射影 fibration（BM 命題 4.1）。
方針：直和への評価と積の比較同型の逆射の合成として全次数全射性を示す。
規約：値域の cofibrancy を要求しない。
使われ方：good path object の評価条件を与える。 -/
lemma prepathAlgebra_p_projectiveFibration (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P)
    (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) (B : P.Algebra) :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.prepathAlgebra hP I B).p.hom := by
  have h : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.prepathAlgebra hP I B).p =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationPair hP I B ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductIso B B).inv := by
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.prepathAlgebra_p_compare, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  intro n
  have : IsIso (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductIso B B)).inv.f n) := by
    change IsIso (((HomologicalComplex.eval (ModuleCat A) (.up ℤ) n).mapIso
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductIso B B))).inv)
    infer_instance
  exact ((ModuleCat.epi_iff_surjective _).1 (inferInstance :
    Epi (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductIso B B)).inv.f n))).comp
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationPair_projectiveFibration hP I B n)

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.weakEquivalenceStructure _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.fibrationStructure

/-- 概要：余代数区間は全代数の path object を与える（BM 命題 4.1）。
方針：既存の prepath object に定数射の底の擬同型性を加える。
規約：忘却の逆像で弱同値を定め、モデル構造の存在は使わない。
使われ方：fibrations.llp の射のホモトピー逆を構成する。 -/
def pathAlgebra (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) (B : P.Algebra) :
    PathObject B where
  __ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.prepathAlgebra hP I B
  weakEquivalence_ι := ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraConstantNat_quasiIso hP I B⟩

/-- 概要：区間から作った全代数の path object は good（BM 命題 4.1）。
方針：積への評価の底の全次数全射性を使う。
規約：入力の代数は任意。
使われ方：転送の acyclicity に必要な path object の持ち上げを保証する。 -/
instance pathAlgebra_isGood (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit)
    (B : P.Algebra) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.pathAlgebra hP I B).IsGood where
  fibration_p := ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.prepathAlgebra_p_projectiveFibration hP I B⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval
