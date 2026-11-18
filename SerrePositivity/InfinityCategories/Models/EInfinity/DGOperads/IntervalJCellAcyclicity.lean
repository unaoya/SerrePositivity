module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IntervalAcyclicity
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FreeAlgebraAdjunction
public import SerrePositivity.HomotopicalAlgebra.Transfer.Right

/-!
模型。文献の定義との比較は後で
# 自由像の J-cell 射の acyclicity

概要：Berger–Moerdijk 命題 4.1 の区間から自由像の相対 J-cell 射の擬同型性を得る。
方針：自由・忘却随伴で右持ち上げ類を同定し、左持ち上げ類の閉性を使う。
規約：任意の始域を許し、小対象性とモデル構造の存在は仮定しない。
使われ方：右転送定理の acyclicity の入力を供給する。
-/

@[expose] public section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval

open _root_.CategoryTheory _root_.HomologicalComplex

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：自由像 J の右持ち上げ類は底の射影 fibration（BM 命題 4.1）。
方針：随伴の持ち上げ対応と複体の生成 trivial cofibration の右類を使う。
規約：代数のモデル構造や区間は不要。
使われ方：自由像の相対 J-cell 射を fibrations.llp に含める。 -/
lemma freeGeneratingTrivialCofibrations_rlp (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) :
    ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A).strictMap P.freeAlgebraFunctor).rlp =
      (_root_.SerrePositivity.ProjectiveModel.projectiveFibrations A).inverseImage (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) := by
  rw [_root_.SerrePositivity.ModelGeneration.strictMap_rlp P.freeAlgebraAdjunction,
    _root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations_rlp]

/-- 概要：自由像 J の生成する左持ち上げ類の射は底で擬同型（BM 命題 4.1）。
方針：右持ち上げ類を忘却の逆像に同定し、区間の path object 論法を使う。
規約：始域の cofibrancy と小対象性を要求しない。
使われ方：相対 J-cell 射の acyclicity の終段となる。 -/
lemma freeGeneratingTrivialCofibrations_llp_le (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P)
    (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) :
    ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A).strictMap P.freeAlgebraFunctor).rlp.llp ≤
      (quasiIso (ModuleCat A) (.up ℤ)).inverseImage (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.freeGeneratingTrivialCofibrations_rlp]
  intro X Y f hf
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.fibrations_llp_quasiIso hP I f hf

/-- 概要：自由像 J の相対 cell 射は任意の始域について底で擬同型（BM 命題 4.1）。
方針：左持ち上げ類の余積・押し出し・超限合成による閉性を使う。
規約：小対象性と代数のモデル構造の存在を仮定しない。
使われ方：Transfer.Right.rightTransfer の acyclicity の入力そのものを与える。 -/
lemma freeGeneratingTrivialCofibrations_cell_acyclicity (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P)
    (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit) :
    MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u}
        ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A).strictMap P.freeAlgebraFunctor)).pushouts ≤
      (quasiIso (ModuleCat A) (.up ℤ)).inverseImage (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) := by
  apply le_trans ?_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.freeGeneratingTrivialCofibrations_llp_le hP I)
  rw [MorphismProperty.transfiniteCompositions_le_iff, MorphismProperty.pushouts_le_iff,
    MorphismProperty.coproducts_le_iff]
  exact MorphismProperty.le_llp_rlp _

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval
