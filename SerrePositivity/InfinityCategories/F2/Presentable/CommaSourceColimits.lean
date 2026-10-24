module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeRestrictionMappingCriterion
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaHom
public import SerrePositivity.InfinityCategories.Stable.ColimitRestriction
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.PrecompositionMappingPair

/-!
概要：oriented comma の始域図式の余極限を元の図式へ戻す。
方針：恒等矢印の包含による Hom 同値を全パラメータで余錐空間へ移す。
規約：comma 射影自体を圏同値とは仮定しない。
使われ方：小余積と幾何学的実現を合成した図式の元の余極限の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：comma の始域と終域から引いた二つの図式の Hom は元の包含で全単射になる。
方針：元の comma の Hom 同値から端点の等式による共役を消去する。
規約：元の制限関手の作用そのものを比較する。
使われ方：定値標的の全パラメータの写像空間。 -/
lemma commaInclusion_homMap_bijective {K C X : SSet.{u}} (δ : K ⟶ C)
    (F : K ⟶ X) (G : C ⟶ X) :
    Function.Bijective
      ((hoFunctor.map ((pre (F1B.kanLeftCommaInclusion δ)).app X)).toFunctor.map :
        FunctorHom (F1B.kanLeftCommaSource δ ≫ F) (F1B.kanLeftCommaProjection δ ≫ G) → _) := by
  let E := F1B.kanFunctorHomCongr
    (U := F1B.kanLeftCommaInclusion δ ≫ (F1B.kanLeftCommaSource δ ≫ F))
    (V := F1B.kanLeftCommaInclusion δ ≫ (F1B.kanLeftCommaProjection δ ≫ G))
    (by rw [← Category.assoc, F1B.kanLeftCommaInclusion_source, Category.id_comp])
    (by rw [← Category.assoc, F1B.kanLeftCommaInclusion_projection])
  have h := (F1B.kanLeftCommaHomEquiv δ F G).bijective
  change Function.Bijective (E ∘
    ((hoFunctor.map ((pre (F1B.kanLeftCommaInclusion δ)).app X)).toFunctor.map :
      FunctorHom (F1B.kanLeftCommaSource δ ≫ F) (F1B.kanLeftCommaProjection δ ≫ G) → _)) at h
  exact h.of_comp_left E.injective

/-- 概要：元の始域図式について comma の恒等矢印包含は全余錐制限の同値を与える。
方針：全パラメータの Hom 全単射を元の定値標的への pinched 作用へ移す。
規約：始域図式を固定し、comma の任意の図式については主張しない。
使われ方：comma 上の余極限から元の図式への存在の移送。 -/
lemma commaSource_sliceUnderRestrict_equivalence
    {K C X : SSet.{u}} [Quasicategory X] (δ : K ⟶ C) (F : K ⟶ X) :
    IsQCatEquivalence (sliceUnderRestrict (F1B.kanLeftCommaSource δ ≫ F)
      (F1B.kanLeftCommaInclusion δ)) := by
  apply sliceUnderRestrict_equivalence_of_constantPinched
  intro z
  have h := F1B.precomposition_pinchedHomMap_equivalence_of_constantFamily
    (F1B.kanLeftCommaInclusion δ) (F1B.kanLeftCommaSource δ ≫ F)
    (F1B.kanLeftCommaProjection δ ≫ SSet.const z) (fun A ↦
      commaInclusion_homMap_bijective δ (F ≫ constantFunctorMap A X)
        (SSet.const z ≫ constantFunctorMap A X))
  simpa only [SSet.comp_const] using h.isQCatEquivalence

/-- 概要：comma の同じ始域図式が余極限を持てば元の図式も余極限を持つ。
方針：全余錐制限の同値で普遍余錐を制限し、包含と射影の合成を計算する。
規約：元の図式 F の余極限を結論する。
使われ方：相対 join を用いた小余極限の構成の最終段。 -/
lemma hasColimit_of_commaSource {K C X : SSet.{u}} [Quasicategory X]
    (δ : K ⟶ C) (F : K ⟶ X) (h : HasColimit (F1B.kanLeftCommaSource δ ≫ F)) :
    HasColimit F := by
  obtain ⟨c, hc⟩ := h
  have hr := ((commaSource_sliceUnderRestrict_equivalence δ F).choose.isInitialVertex_iff c).mp hc
  have h' : HasColimit (F1B.kanLeftCommaInclusion δ ≫ (F1B.kanLeftCommaSource δ ≫ F)) :=
    ⟨c.restrict (F1B.kanLeftCommaInclusion δ), hr⟩
  simpa only [← Category.assoc, F1B.kanLeftCommaInclusion_source, Category.id_comp] using h'

end SerrePositivity.InfinityCategories.F2.Presentable
