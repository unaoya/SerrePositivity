module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleIndRepresentation
public import SerrePositivity.InfinityCategories.F2.Presentable.RelativeHomModel
public import SerrePositivity.InfinityCategories.F2.Presentable.FullyFaithfulHomComparison
public import
  SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningInfinityEquivalence
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices

/-!
概要：accessible 圏の元の各対象からの Hom を小さい空間値の全関手で表す。
方針：Ind 包含と straightening の逆で相対 Hom の模型へ送り、全自然な比較を合成する。
規約：点ごとの小さい写像空間を選ぶだけでなく、一つの元の全関手を構成する。
使われ方：随伴関手定理に必要な小さい空間値の Hom 合成関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：left fibration の全圏への充満忠実模型は元の対象の小さい全共変 Hom を与える。
方針：元の対象の像の相対 Hom 評価関手を引き戻す。
規約：全自然比較は元の大きい共変 Hom と指定宇宙変更の間のもの。
使われ方：accessible 圏の小さい Hom 関手の構成。 -/
lemma exists_smallCovariantHom_of_leftFibrationModel
    {B : SSet.{u}} {C : SSet.{u + 1}} [Quasicategory C]
    (j : C ⟶ LeftFibrationInfinity B) (hj : IsFullyFaithful j) (x : C _⦋0⦌) :
    ∃ H : C ⟶ SpaceInfinity.{u}, Nonempty (FunctorIso (covariantRepresentableInfinity x)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram)) := by
  let q := coherentNerveObject (j.app (Opposite.op ⦋0⦌) x)
  have hq : coherentNerveVertex q = j.app (Opposite.op ⦋0⦌) x :=
    coherentNerveVertex_object _
  have hr : FunctorIso (covariantRepresentableInfinity (j.app (Opposite.op ⦋0⦌) x))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (leftFibrationCoherentEvaluation q.val) ≫
        Compact.spaceUniverseDiagram) := by
    rw [← hq]
    exact relativeHom_covariantModelIso q
  refine ⟨j ≫ leftFibrationCoherentEvaluation q.val, ⟨?_⟩⟩
  have h := covariantHomComparisonIso j hj x ≪≫
    FunctorIso.precomp hr ((SSet.uliftFunctor.{u + 2, u + 1}).map j)
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using h

/-- 概要：accessible 圏の各対象の元の全共変 Hom は小さい空間値の一つの関手を持つ。
方針：元の小さい Ind 模型を left fibrations の全圏へ充満忠実に送って比較する。
規約：元の対象と元の全 Hom 関手を厳密に保持する。
使われ方：空間値関手の余表現可能性を一般の随伴関手へ適用する。 -/
lemma IsAccessible.exists_smallCovariantHom {C : SSet.{u + 1}} [Quasicategory C]
    (hC : IsAccessible C) (x : C _⦋0⦌) :
    ∃ H : C ⟶ SpaceInfinity.{u}, Nonempty (FunctorIso (covariantRepresentableInfinity x)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map H ≫ Compact.spaceUniverseDiagram)) := by
  obtain ⟨κ, hκ⟩ := hC
  obtain ⟨A, hA, ⟨e⟩⟩ := hκ.exists_indEquivalence
  have := hA
  let s : QCatEquivalence (LeftFibrationInfinity A.op) (PresheafInfinity A) :=
    leftStraighteningInfinityEquivalence A.op
  let j := e.inv ≫ Ind.indInclusionPresheaf κ A ≫ s.inv
  have hj : IsFullyFaithful j := e.symm.isQCatEquivalence.isFullyFaithful.comp
    ((Ind.indInclusionPresheaf_isFullyFaithful κ A).comp s.symm.isQCatEquivalence.isFullyFaithful)
  exact exists_smallCovariantHom_of_leftFibrationModel j hj x

end SerrePositivity.InfinityCategories.F2.Presentable
