module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeRestrictionMappingCriterion
public import SerrePositivity.InfinityCategories.F2.Presentable.CofinalColimitExistence
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinRightHom
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.PrecompositionMappingPair

/-!
概要：相対 join の右端の余極限から、元の全相対 join 図式の余極限を構成する。
方針：右端への全パラメータの Hom 対応を、同じ全余錐制限の同値性へ移す。
規約：構造射の fibration 性や左端の普遍性を仮定しない。
使われ方：次数ごとの小余積と幾何学的実現の合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：右端への制限は、底射影に沿う標的への全 Hom を全単射にする。
方針：既存の右端の Hom 同値から、端点の等式による輸送を消去する。
規約：元の制限の関手作用そのものを扱う。
使われ方：定値パラメータ族の制限の写像空間比較。 -/
lemma relativeJoinRight_homMap_bijective {K C X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ C) (H : relativeJoin p (𝟙 C) ⟶ X) (G : C ⟶ X) :
    Function.Bijective
      ((hoFunctor.map ((pre (relativeJoinInr p (𝟙 C))).app X)).toFunctor.map :
        FunctorHom H (relativeJoinBaseProjection p (𝟙 C) ≫ G) → _) := by
  let E := F1B.kanFunctorHomCongr
    (U := relativeJoinInr p (𝟙 C) ≫ H) (V := relativeJoinInr p (𝟙 C) ≫
      (relativeJoinBaseProjection p (𝟙 C) ≫ G)) rfl
    (show relativeJoinInr p (𝟙 C) ≫ (relativeJoinBaseProjection p (𝟙 C) ≫ G) = G by
      rw [← Category.assoc, relativeJoinInr_baseProjection, Category.id_comp])
  have h : Function.Bijective (E ∘
      ((hoFunctor.map ((pre (relativeJoinInr p (𝟙 C))).app X)).toFunctor.map :
        FunctorHom H (relativeJoinBaseProjection p (𝟙 C) ≫ G) → _)) := by
    convert (F1B.kanRelativeJoinRightHomEquiv p H G).bijective using 1
    funext α
    simpa only [E, Function.comp_apply, F1B.kanFunctorHomCongr, Iso.homCongr_apply,
      eqToIso.inv, eqToIso.hom, eqToHom_refl, Category.id_comp] using
      (F1B.kanRelativeJoinRightHomEquiv_apply p H G α).symm
  exact h.of_comp_left E.injective

/-- 概要：相対 join の右端に沿う元の全余錐制限は同値。
方針：全パラメータの Hom 全単射から定値標的への pinched 作用を同値とする。
規約：左端の普遍性は要求しない。
使われ方：右端の幾何学的実現から全相対 join の余極限を戻す。 -/
lemma relativeJoinRight_sliceUnderRestrict_equivalence
    {K C X : SSet.{u}} [Quasicategory X] (p : K ⟶ C)
    (H : relativeJoin p (𝟙 C) ⟶ X) :
    IsQCatEquivalence (sliceUnderRestrict H (relativeJoinInr p (𝟙 C))) := by
  apply sliceUnderRestrict_equivalence_of_constantPinched
  intro z
  have h := F1B.precomposition_pinchedHomMap_equivalence_of_constantFamily
    (relativeJoinInr p (𝟙 C)) H
    (relativeJoinBaseProjection p (𝟙 C) ≫ SSet.const z) (fun A ↦
      relativeJoinRight_homMap_bijective p (H ≫ constantFunctorMap A X)
        (SSet.const z ≫ constantFunctorMap A X))
  simpa only [SSet.comp_const] using h.isQCatEquivalence

/-- 概要：相対 join の右端の図式に余極限があれば、全図式も余極限を持つ。
方針：同じ全余錐制限の逆で右端の普遍余錐を戻す。
規約：元の全図式 H の余極限を結論する。
使われ方：小余積と幾何学的実現からの小余極限。 -/
lemma relativeJoin_hasColimit_of_right
    {K C X : SSet.{u}} [Quasicategory X] (p : K ⟶ C)
    (H : relativeJoin p (𝟙 C) ⟶ X)
    (h : HasColimit (relativeJoinInr p (𝟙 C) ≫ H)) : HasColimit H :=
  hasColimit_of_sliceUnderRestrict_equivalence _ H
    (relativeJoinRight_sliceUnderRestrict_equivalence p H) h

end SerrePositivity.InfinityCategories.F2.Presentable
