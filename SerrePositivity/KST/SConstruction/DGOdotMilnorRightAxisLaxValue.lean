module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisBaseValue
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNullNativeValue
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityLaxArrowBase
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityHomTargetDiagonal
public import SerrePositivity.KST.SConstruction.FunctorIsoEquivalenceReflection

/-!
概要：実右軸と同じ逆回転基底の恒等 gluing を、元 resolved 商値の恒等 lax 圏へ移す。
方針：元 native 全比較を同じ ν 同値と二段包絡評価で挟む。
規約：元実中央頂点・元対角・元 resolved 商を保持し、別模型を選ばない。
使われ方：共通実長方形の右面における中央頂点と指定対角境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "eU" => dgOdotMilnorRightAxisIdentityBaseNativeValueEquivalence R d
local notation "eL" => dgOdotMilnorRightAxisTargetNativeValueEquivalence R d
local notation "eB" => dgOdotMilnorRightAxisBaseValueEquivalence R d
local notation "eN" => dgIdentityHomGluingNullLaxEquivalence R (U)

/-- 概要：元逆回転基底の native 値を同じ resolved 商の固定 ν 値へ比較する。
方針：元 Yoneda 比較と元二段包絡評価を合成する。
規約：同じ元評価を保持。使われ方：恒等 lax 全比較の基底変更。 -/
def dgOdotMilnorRightAxisNativeResolvedValueEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U)) (Q).obj := (eU).trans (eB)

/-- 概要：実中央頂点の固定 ν 値から同じ resolved 商値の恒等 lax 圏への全同値。
方針：同じ native 恒等 gluing 比較を元基底値同値で基底変更する。
規約：同じ順逆と指定往復則。使われ方：実右面の中央頂点比較。 -/
def dgOdotMilnorRightAxisCompletedGluingEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorRightAxisInput R d)).obj
    (laxCategory (𝟙 (Q)) (𝟙 (Q))).obj :=
  (eL).symm.trans ((eN).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseEquivalence
    (dgOdotMilnorRightAxisNativeResolvedValueEquivalence R d)))

/-- 概要：元実対角辺は同じ completed 中央同値の下で絶対恒等対角へ全比較される。
方針：元 ν 自然性・native 対角比較・同じ lax 基底変更の対角則を合成する。
規約：元対角始域の二段値同値を保持。使われ方：右面の指定包含比較の元対角側。 -/
def dgOdotMilnorRightAxisCompletedDiagonalComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgKInputNuMap R (dgOdotMilnorRightAxisIdentityDiagonalInputMap R d)).hom ≫
      (dgOdotMilnorRightAxisCompletedGluingEquivalence R d).hom)
    ((eB).hom ≫ (IdentityLax.exactDiagonal (Q)).hom) := by
  have assocFour {A B C D E : SSet.{u + 1}}
      (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (e : D ⟶ E) :
      (a ≫ (b ≫ c)) ≫ e = a ≫ b ≫ (c ≫ e) := by
    simp only [Category.assoc]
  have nativeDiagonalSource (T : Type (u + 1)) [DGCategory R T] [Small.{u} T] :
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeDiagonal.{u, 0} R T) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingDiagonal R T) := rfl
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorRightAxisIdentityDiagonal R d)
  let a := (dgKInputNuMap R (dgOdotMilnorRightAxisIdentityDiagonalInputMap R d)).hom
  let t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseEquivalence
    (dgOdotMilnorRightAxisNativeResolvedValueEquivalence R d)
  let g := (dgOdotMilnorRightAxisCompletedGluingEquivalence R d).hom
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((eU).hom ≫ a ≫ g) (i ≫ (eL).hom ≫ g) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      ((dgOdotMilnorRightAxisIdentityDiagonalNuComparison R d).postcomp g)
      (Category.assoc _ _ _) (Category.assoc _ _ _)
  have h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ (eL).hom ≫ g) (i ≫ (eN).hom ≫ t.hom) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (eL).homInvIso i).postcomp ((eN).hom ≫ t.hom))
      (assocFour i (eL).hom (eL).inv ((eN).hom ≫ t.hom))
      (congrArg (fun k => k ≫ ((eN).hom ≫ t.hom)) (Category.comp_id i))
  have h₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ (eN).hom ≫ t.hom)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u + 1}) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U)) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U))) ≫ t.hom) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityNativeDiagonalIso.{u, 0} R (U)).postcomp t.hom)
      ((Category.assoc _ _ _).trans
        (congrArg (fun k => k ≫ (eN).hom ≫ t.hom) (nativeDiagonalSource (U)))) rfl
  have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u + 1}) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U)) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (U))) ≫ t.hom =
      (eU).hom ≫ (eB).hom ≫ (IdentityLax.exactDiagonal (Q)).hom :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseEquivalence_diagonal
      (dgOdotMilnorRightAxisNativeResolvedValueEquivalence R d)
  apply functorIsoReflectPreEquivalence (eU)
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (h₁.trans (h₂.trans h₃)) rfl ht

end SerrePositivity.KST.SConstruction
