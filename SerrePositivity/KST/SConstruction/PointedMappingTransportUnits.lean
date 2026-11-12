module
public import SerrePositivity.KST.SConstruction.PointedExtensionTransport

/-! # 写像空間の移送の恒等変数
概要：一方の変数が恒等の移送を通常の前合成・後合成と同定する。
方針：閉構造の pre と内部 Hom の関手の単位法則を使う。
規約：全パラメーターの厳密等号。
使われ方：混合選択空間から合成族への射の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet
open Spectra.PointedMapping

/-- 源を固定した移送は標的の後合成。 -/
lemma pointedMappingTransport_source_id {B Z Z' : PointedSimplicialSet.{u}} (z : Z ⟶ Z') :
    pointedMappingTransport (𝟙 B) z = (PointedObject.basedHomMap B z).right := by
  have hp : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (𝟙 B) Z' = 𝟙 _ := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, pre_id]
    rfl
  simp only [pointedMappingTransport, hp, Category.comp_id]

/-- 標的を固定した移送は源の前合成。 -/
lemma pointedMappingTransport_target_id {B B' Z : PointedSimplicialSet.{u}} (b : B' ⟶ B) :
    pointedMappingTransport b (𝟙 Z) = (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed b Z).right := by
  have hz : PointedObject.basedHomMap B (𝟙 Z) = 𝟙 _ :=
    (PointedObject.basedHomFunctor B).map_id Z
  simp only [pointedMappingTransport, hz, Category.id_comp]

end SerrePositivity.KST.SConstruction
