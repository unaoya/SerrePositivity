module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead
public import SerrePositivity.KST.Spectra.PostMappingLifts

/-!
概要：点つき内部 Hom は Kan 複体間の全基点 π_* 同型を標的変数で保存する。
方針：mapping path の二つの全単射 RLP 射へ還元し、内部 Hom の RLP 保存を適用する。
規約：源 A の有限性や Kan 性は不要。HT-KQ を使わない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。内部 Hom と Ω 列の構成。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき写像空間の後合成は Kan な標的間の全基点 π_* 同型を保つ。
方針：mapping path の右因子と源射影の RLP を内部 Hom へ移し、切断の合成を打ち消す。
規約：零次数を含む全基点での主張。源 A に条件を課さない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。Ω 条件の内部 Hom への移送。 -/
theorem post_piIsomorphism (A : PointedSimplicialSet.{u})
    {X Y : PointedSimplicialSet.{u}} [KanComplex X.right] [KanComplex Y.right]
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (PointedObject.basedHomMap A f).right := by
  let F := ihom A
  let : KanComplex (F.obj X).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex A X
  let : KanComplex (F.obj Y).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex A Y
  let : KanComplex (F.obj (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f)).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f)
  let u := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit f
  let r := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f
  let p := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f
  have hr : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (F.map r).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (post_rlp_monomorphisms A r (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction_rlp f))
  have hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (F.map p).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _
      (post_rlp_monomorphisms A p (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism f hf))
  have hur : F.map u ≫ F.map r = 𝟙 (F.obj X) := by
    rw [← F.map_comp, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_retraction, F.map_id]
  have hu : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (F.map u).right := by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := (F.map r).right) _ hr
    have h : (F.map u).right ≫ (F.map r).right = 𝟙 (F.obj X).right :=
      congrArg Under.Hom.right hur
    rw [h]
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _
  have hup : F.map u ≫ F.map p = F.map f := by
    rw [← F.map_comp, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_projection]
  have h : (F.map u).right ≫ (F.map p).right = (F.map f).right :=
    congrArg Under.Hom.right hup
  have hc := hu.comp hp
  rw [h] at hc
  exact hc

end

end SerrePositivity.KST.Spectra.PointedMapping
