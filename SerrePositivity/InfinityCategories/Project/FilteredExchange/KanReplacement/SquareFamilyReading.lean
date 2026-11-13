module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeValEquality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeCompletion
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorVertexCone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseHorns

/-!
概要：全四角形族の頂点を読み戻し、同じ引き戻し錐・押し出し余錐へ制限する。
方針：前合成と関手頂点の全単射の往復、ホーン形状の同型を使う。
規約：元の四角形の全単体を保持する。宇宙持ち上げは形状だけに明示する。
使われ方：Ind の点ごとの filtered 補完に有限交換と余極限同士の交換を適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 関手頂点の元の実四角形。 -/
def functorVertexSquare {X : SSet.{u}}
    (v : ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm v

/-- 元の実四角形の読み戻しは、全空間の後合成と交換する。 -/
lemma functorVertexSquare_postcompose {X Y : SSet.{u}}
    (v : ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) _⦋0⦌) (F : X ⟶ Y) :
    functorVertexSquare (((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).map F).app
      (Opposite.op ⦋0⦌) v) = functorVertexSquare v ≫ F := by
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).surjective v
  rfl

/-- 小さい cospan の持ち上げた錐と、大きい宇宙の元の正方形の実同型。 -/
def uliftCospanSquareReadingIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj (horn 2 2)) ≅
      (Δ[1] : SSet.{max u v}) ⊗ Δ[1] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (Iso.refl Δ[0]) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, v} 2 2) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso

/-- 小さい cospan の持ち上げた錐を、大きい宇宙の実四角形へ同定する。 -/
def uliftCospanSquareReading :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj (horn 2 2)) ⟶
      (Δ[1] : SSet.{max u v}) ⊗ Δ[1] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, v} 2 2).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom

/-- 持ち上げた cospan への読み戻しの極限性は、元の実四角形の引き戻し性。 -/
lemma functorVertexSquare_pullback_iff {X : SSet.{max u v}}
    (v : ((ihom ((Δ[1] : SSet.{max u v}) ⊗ Δ[1])).obj X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone
      (((pre uliftCospanSquareReading.{u, v}).app X).app (Opposite.op ⦋0⦌) v)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (functorVertexSquare v) := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (functorVertexSquare v)
  have he : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone
      (((pre uliftCospanSquareReading.{u, v}).app X).app (Opposite.op ⦋0⦌) v)).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, v} 2 2).hom).val := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexMap_precomp]
    exact Category.assoc _ _ _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ he).trans
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_restrict_iff_of_isIso c (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, v} 2 2).hom)

/-- 元の span への読み戻しの余極限性は、同じ実四角形の押し出し性。 -/
lemma functorVertexSquare_pushout_iff {X : SSet.{u}}
    (v : ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.functorVertexCocone
      (((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom).app X).app (Opposite.op ⦋0⦌) v)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (functorVertexSquare v) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isColimitCone_iff_of_coconeMap_eq
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexMap_precomp _ v

end SerrePositivity.InfinityCategories.Project.FilteredExchange
