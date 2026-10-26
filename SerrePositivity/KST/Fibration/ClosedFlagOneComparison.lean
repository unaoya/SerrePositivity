module
public import SerrePositivity.KST.Fibration.ClosedFlagOneEquivalence
public import SerrePositivity.KST.Fibration.ClosedFlagFiniteComparison
public import SerrePositivity.KST.SConstruction.RelativeMultiRealizationAdditivity

/-!
概要：閉じた P 旗の有限積比較の一辺の場合を、元の相対加法性へ接続する。
方針：同じ共通補完と元の初期頂点の二射影を回収する。
規約：B と P 以外の仮定なし。使われ方：全有限旗の共通帰納の初段。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
open Relative
variable {B : StableModel.{u}} (P : ClosedStablePredicate B)

/-- 概要：同じ cofiber 切断の subobject は元の矢印の source 評価。
方針：元の cofiber 射影の厳密 source 回収と切断式を合成する。
規約：同じ補完選択。使われ方：有限旗比較の初期成分の照合。 -/
theorem closedArrowCofiber_section_source :
    (closedArrowCofiberEquivalence P).inv ≫
      relativeCofiberSubobject (ClosedStablePredicate.top B) P = closedArrowSource P := by
  rw [← closedCofiberProjection_source, ← Category.assoc]
  change ((closedArrowCofiberEquivalence P).inv ≫
    (closedArrowCofiberEquivalence P).hom) ≫ closedArrowSource P = _
  rw [closedArrowCofiberEquivalence_section, Category.id_comp]

/-- 概要：同じ一辺の共通補完は、元の初期頂点を厳密回収する。
方針：元の source 回収を全頂点の包含へ合成する。
規約：同じ初期評価。使われ方：元の相対加法性の第一成分。 -/
theorem closedFlagOne_subobject :
    (closedFlagEdge P (𝟙 ⦋1⦌) ≫ (closedArrowCofiberEquivalence P).inv) ≫
      relativeCofiberSubobject (ClosedStablePredicate.top B) P ≫
        (closedTopExactIso B).hom = closedFlagVertex P ⦋1⦌ 0 := by
  rw [Category.assoc, ← Category.assoc (closedArrowCofiberEquivalence P).inv,
    closedArrowCofiber_section_source]
  apply Subtype.ext
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：同じ一辺の実二成分比較は全正反復で局所化同型。
方針：元の一辺完全同値・相対加法性・全頂点の完全同型を合成する。
規約：元の共通 cofiber を保持。使われ方：有限旗初段の同値性。 -/
theorem closedFlagOnePair_localized_isIso (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (lift ((multiRealizationFunctor (r + 1)).map (closedFlagVertex P ⦋1⦌ 0))
        ((multiRealizationFunctor (r + 1)).map (closedFlagCofiber P (𝟙 ⦋1⦌))))) := by
  let F := multiRealizationFunctor (r + 1)
  let a := F.map (closedFlagEdge P (𝟙 ⦋1⦌)) ≫
    F.map (closedArrowCofiberEquivalence P).inv ≫
      relativeMultiRealizationAdditivityMap (r + 1) (ClosedStablePredicate.top B) P ≫
        (F.map (closedTopExactIso B).hom ▷ F.obj (closedStableModel P))
  have ha : a = lift (F.map (closedFlagVertex P ⦋1⦌ 0))
      (F.map (closedFlagCofiber P (𝟙 ⦋1⦌))) := by
    dsimp only [a]
    unfold relativeMultiRealizationAdditivityMap
    rw [lift_whiskerRight, comp_lift, comp_lift]
    apply congrArg₂ lift
    · rw [← F.map_comp, ← F.map_comp, ← F.map_comp]
      exact congrArg F.map (by
        simpa only [Category.assoc] using closedFlagOne_subobject P)
    · rw [← F.map_comp, ← F.map_comp]
      apply congrArg F.map
      simp only [closedFlagCofiber, closedFlagCofiberCompletion, Category.assoc]
  have : IsIso (AnodyneHomotopy.anodyneQ.map (F.map (closedFlagEdge P (𝟙 ⦋1⦌)))) :=
    multiRealization_map_localized_isIso_of_equivalence r (closedFlagOneEquivalence P)
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (F.map (closedArrowCofiberEquivalence P).inv)) :=
    multiRealization_map_localized_isIso_of_equivalence r (closedArrowCofiberEquivalence P).symm
  have := relativeMultiRealizationAdditivityMap_localized_isIso r (ClosedStablePredicate.top B) P
  rw [← ha]
  dsimp only [a]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration
