module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInitialEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPrecompositionComparison
public import SerrePositivity.InfinityCategories.Core.SliceMap

/-!
概要：始対象を保つ実制限、および任意の関手の coslice 作用は left fibration の全相対 Hom を保つ。
方針：元の始対象での二つの評価の自明 Kan 性と、前合成・評価の厳密な可換式を使う。
規約：底の関手に充満忠実性を要求しない。
使われ方：P-12 の指定 Yoneda 単位の各評価における左 Kan 比較を判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：始対象とその像が始対象なら、left fibration の実相対 Hom の制限は同値。
方針：両始対象での評価を自明 Kan fibration とし、可換三角形に二対三則を適用する。
規約：制限写像そのものを判定する。使われ方：coslice による Hom 普遍性の回収。 -/
lemma relativeHomRestriction_isQCatEquivalence_of_initialVertices
    {T S E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (a : S ⟶ B) (i : T ⟶ S)
    (v : T _⦋0⦌) (hv : IsInitialVertex v)
    (hi : IsInitialVertex (i.app (Opposite.op ⦋0⦌) v)) :
    IsQCatEquivalence (relativeFunctorPre p a i) := by
  have ht := relativeFunctorEvaluate_initial_trivialKanFibration p (i ≫ a) v hv
  have hs := relativeFunctorEvaluate_initial_trivialKanFibration p a
    (i.app (Opposite.op ⦋0⦌) v) hi
  have : TrivialKanFibration (relativeFunctorEvaluate p (i ≫ a) v) := ht
  have : TrivialKanFibration (relativeFunctorEvaluate p a
    (i.app (Opposite.op ⦋0⦌) v)) := hs
  apply (isQCatEquivalence_of_trivialKanFibration
    (relativeFunctorEvaluate p (i ≫ a) v)).cancel_right
  rw [relativeFunctorPre_evaluate]
  exact isQCatEquivalence_of_trivialKanFibration _

/-- 概要：任意の関手の coslice 作用は元の恒等余錐を始対象へ送る。
方針：像の全余錐写像が同じ像頂点での定値写像であることを計算する。
規約：標的 coslice の底を元の合成写像として保つ。
使われ方：元の関手に沿う co-Yoneda の Hom 制限の同値性。 -/
lemma coslicePostcomp_identity_isInitial
    {A C : SSet.{u}} [Quasicategory C] (F : A ⟶ C) (a : A _⦋0⦌) :
    IsInitialVertex ((sliceUnderPostcomp (SSet.yonedaEquiv.symm a) F).app
      (Opposite.op ⦋0⦌) (cosliceIdentityCone a)) := by
  apply isColimitCone_of_point_constant _ (F.app (Opposite.op ⦋0⦌) a)
  change SSet.const a ≫ F = _
  exact SSet.const_comp _ _

/-- 概要：任意の元の関手の coslice 作用による実相対 Hom の制限は同値。
方針：元の恒等余錐とその像が始対象であることを全相対 Hom の評価へ渡す。
規約：A・C は quasicategory、F は任意。使われ方：指定 Hom 単位の各評価の左 Kan 比較。 -/
lemma cosliceHomRestriction_isQCatEquivalence
    {A C E : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (a : A _⦋0⦌) (p : E ⟶ C) [LeftFibration p] :
    IsQCatEquivalence (relativeFunctorPre p
      (sliceUnderProjection (SSet.yonedaEquiv.symm a ≫ F))
      (sliceUnderPostcomp (SSet.yonedaEquiv.symm a) F)) :=
  relativeHomRestriction_isQCatEquivalence_of_initialVertices p _ _ (cosliceIdentityCone a)
    (cosliceIdentityCone_isInitialVertex a) (coslicePostcomp_identity_isInitial F a)

end SerrePositivity.InfinityCategories.F2.Presentable
