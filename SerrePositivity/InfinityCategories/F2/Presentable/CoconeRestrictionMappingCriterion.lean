module
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeTransformationEquivalence

public import SerrePositivity.InfinityCategories.F1.Ind.CoconeTransformationRestriction
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostHomCriterion
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.Stable.InitialTransport

/-!
概要：定値図式への写像空間の制限だけから全余錐制限の同値性を得る。
方針：元の pinched 作用を区間作用へ移し、全余錐空間の各 fiber で比較する。
規約：関手圏全体の充満忠実性を要求しない。
使われ方：相対 join の右端の余極限から元の図式の余極限を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：指定 pinched Hom 作用の同値性は、同じ正規化した区間 Hom 作用の同値性を与える。
方針：二つの模型の自然な比較を同値性の二者三者性で消去する。
規約：元の端点の等式を全て保持する。
使われ方：指定された定値標的への変換空間の比較。 -/
lemma intervalMappingPostOfEq_equivalence_of_pinched
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y)
    (x y : X _⦋0⦌) {x' y' : Y _⦋0⦌} (hx : p.app _ x = x') (hy : p.app _ y = y')
    (hp : IsQCatEquivalence (pinchedHomMap p x y)) :
    IsQCatEquivalence (intervalMappingPostOfEq p x y hx hy) := by
  apply (pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).cancel_left
  rw [← pinchedHomToIntervalMappingSpace_postOfEq]
  exact (hp.comp (qCatEquivalenceOfIso
    (eqToIso (congrArg₂ (fun a b ↦ pinchedHom a b) hx hy))).isQCatEquivalence).comp
    (pinchedHomToIntervalMappingSpace_isQCatEquivalence x' y')

/-- 概要：定値標的への pinched 作用が全頂点で同値なら、全余錐の制限も同値。
方針：元の定値変換の制限を同値とし、終点固定余錐の全 fiber へ戻す。
規約：元の図式 F に関する比較だけを仮定する。
使われ方：相対 join の右包含に沿う余錐存在の比較。 -/
lemma sliceUnderRestrict_equivalence_of_constantPinched
    {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B) (F : B ⟶ X)
    (h : ∀ z : X _⦋0⦌, IsQCatEquivalence (pinchedHomMap ((pre i).app X)
      (functorVertex F) (functorVertex (SSet.const z)))) :
    IsQCatEquivalence (sliceUnderRestrict F i) := by
  apply isQCatEquivalence_of_leftFibration_fibers (sliceUnderProjection F)
    (sliceUnderProjection (i ≫ F)) (sliceUnderRestrict F i) rfl
  intro z
  have ht : IsQCatEquivalence (Ind.constantTransformationRestriction i F z) :=
    intervalMappingPostOfEq_equivalence_of_pinched _ _ _ _ _ (h z)
  have hc := (coconeTransformationMap_isQCatEquivalence F z).comp ht
  rw [← Ind.coconeTransformationMap_restrict i F z] at hc
  exact (coconeTransformationMap_isQCatEquivalence (i ≫ F) z).cancel_right hc

end SerrePositivity.InfinityCategories.F2.Presentable
