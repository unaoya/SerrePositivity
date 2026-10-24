module

public import SerrePositivity.InfinityCategories.F2.Presentable.FullyFaithfulHomComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.NativeUniverseContinuity
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulIsoRecovery
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence

/-!
概要：小さい空間値関手の元の対象による余表現可能性と同値による移送。
方針：全共変 Hom 比較を使い、同値の前合成の充満忠実性で全自然同型を戻す。
規約：元の関手と元の対象を、同じ指定宇宙変更によって比較する。
使われ方：Ind 模型で構成した余表現対象を元の accessible 圏へ送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：小さい空間値関手が元の対象からの全共変 Hom と全自然に一致すること。
方針：指定した空間の宇宙変更を介して全関手の同型を量化する。
規約：対象は元の圏の頂点。
使われ方：随伴関手定理に必要な余表現可能性の公開述語。 -/
def IsCorepresentableSmallSpaceFunctor {C : SSet.{u + 1}} [Quasicategory C]
    (F : C ⟶ SpaceInfinity.{u}) : Prop :=
  ∃ x : C _⦋0⦌, Nonempty (FunctorIso (covariantRepresentableInfinity x)
    ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ Compact.spaceUniverseDiagram))

/-- 概要：同値へ引き戻した元の関手の余表現対象を、元の標的圏へ移す。
方針：元の全 Hom 比較で制限同型を作り、同値の前合成の充満忠実性で戻す。
規約：関手の値を点ごとに選び直さない。
使われ方：Ind 模型から一般の accessible 圏への余表現可能性。 -/
lemma isCorepresentable_of_equivalence_restriction
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (e : QCatEquivalence C D) (F : D ⟶ SpaceInfinity.{u})
    (hF : IsCorepresentableSmallSpaceFunctor (e.hom ≫ F)) :
    IsCorepresentableSmallSpaceFunctor F := by
  obtain ⟨x, ⟨h⟩⟩ := hF
  let U := SSet.uliftFunctor.{u + 2, u + 1}
  let H := U.map F ≫ Compact.spaceUniverseDiagram
  let R := covariantRepresentableInfinity (e.hom.app (Opposite.op ⦋0⦌) x)
  have hs : FunctorIso (U.map e.hom ≫ R) (U.map e.hom ≫ H) := by
    have h₀ := (covariantHomComparisonIso e.hom e.isQCatEquivalence.isFullyFaithful x).symm ≪≫ h
    simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using h₀
  have hp := (IsQCatEquivalence.ulift.{u + 1, u + 2}
    e.isQCatEquivalence).isPrecompositionEquivalence SpaceInfinity.{u + 1}
  have hR : FunctorIso R H := hp.isFullyFaithful.preimageVertexIso hs
  exact ⟨e.hom.app (Opposite.op ⦋0⦌) x, ⟨hR⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
