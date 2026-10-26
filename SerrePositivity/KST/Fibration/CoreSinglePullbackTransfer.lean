module
public import SerrePositivity.KST.SConstruction.SingleRealizationAdditivity
public import SerrePositivity.KST.Comparison.HomotopyPullbackThreeInputs

/-!
概要：同じ安定模型の実四角形で、一回反復の引き戻しを元の単回 core S 実現へ戻す。
方針：四隅の元の座標同型と完全関手に関する厳密自然性を使う。
規約：同じ四辺を保持。使われ方：閉じた有限旗の単回実自然性の公開。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration

/-- 概要：同じ一回反復実四角形の引き戻しは元の単回 core S 実現でも成立。
方針：正本の四つの実座標同型を同じ比較立方体へ代入する。
規約：抽象的な群同型で代用しない。使われ方：全有限旗の元の F 値四角形。 -/
theorem coreSingleRealization_homotopyPullback_of_multi
    {P X Y B : StableModel.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (sq : CommSq a b f g)
    (h : IsHomotopyPullback ((multiRealizationFunctor 1).map_commSq sq)) :
    IsHomotopyPullback (coreSRealizationFunctor.map_commSq sq) := by
  apply (isHomotopyPullback_iff_of_localized_isIso
    (coreSRealizationFunctor.map_commSq sq) ((multiRealizationFunctor 1).map_commSq sq)
    (coreSingleRealizationIso P).hom (coreSingleRealizationIso X).hom
    (coreSingleRealizationIso Y).hom (coreSingleRealizationIso B).hom
    (coreSingleRealizationIso_naturality a) (coreSingleRealizationIso_naturality b)
    (coreSingleRealizationIso_naturality f) (coreSingleRealizationIso_naturality g)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr h

end SerrePositivity.KST.Fibration
