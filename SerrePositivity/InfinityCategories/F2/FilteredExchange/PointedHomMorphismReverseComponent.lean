module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedHomMorphismDiagonalComponent
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedLeftDiagonalReverseComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedReverseDiagonalValuePresentation

/-!
概要：元の固定射の左値比較を、元の実反転合成 prism の指定比較へ戻す。
方針：curry の固定成分と両端表示の除去を、同じ全係数制限で合成する。
規約：元の実 prism と指定同型の値を保持。使われ方：元の長辺の普遍比較との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K L : KanObject.{u}} (f : K ⟶ L)
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (CategoryTheory.Functor.obj SSet.opFunctor (SimplicialCategory.sHom pointKanObject K))
local notation "H" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (CategoryTheory.Functor.obj SSet.opFunctor (SimplicialCategory.sHom K L))
local notation "v" => ULift.up (SSet.opObjEquiv.symm (functorVertex f))
local notation "D" => pointedReverseKanCompositionTransport_diagonalIso K L
  (fst A H ≫ Iso.hom (uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)))
  (snd A H ≫ Iso.hom (uliftOppositeIso (SimplicialCategory.sHom K L)))
local notation "V" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))

/-- 元の固定射の左値比較は、同じ実反転合成 prism の指定比較の値の同じ制限。 -/
lemma pointedHomMorphismLeftValueComparison_heq_reverse :
    HEq (pointedHomMorphismLeftValueComparison f)
      ((FunctorIso.postcomp D V).precomp (lift (𝟙 A) (SSet.const v))) := by
  exact (pointedHomMorphismLeftValueComparison_heq_diagonal f).trans
    ((pointedLeftHomDiagonalValueIso_precomp_heq_reverse K L (fst A H) (snd A H)
      (lift (𝟙 A) (SSet.const v))).trans
      (pointedReverseKanDiagonalValueIso_precomp_heq_diagonal K L (fst A H) (snd A H)
        (lift (𝟙 A) (SSet.const v))))

/-- 元の二側補間を含む値比較も、同じ元の実反転合成 prism の指定比較の値へ戻る。 -/
lemma pointedHomMorphismValueComparison_heq_reverse :
    HEq (pointedHomMorphismValueComparison f)
      ((FunctorIso.postcomp D V).precomp (lift (𝟙 A) (SSet.const v))) :=
  (heq_of_eq (pointedHomMorphismValueComparison_eq_left f)).trans
    (pointedHomMorphismLeftValueComparison_heq_reverse f)

end SerrePositivity.InfinityCategories.F2
