module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingAcyclic
public import SerrePositivity.KST.Spectra.RawSpectrumPointedPostComposition
public import SerrePositivity.KST.Spectra.MappingPathSequence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead

/-!
概要：一般の Kan 列の段ごとの全基点 π 同型は、BF 源の元の全 Hom への後合成でも π 同型。
方針：元の mapping path 列の二射影の全単射 RLP と厳密な定数区間の切断を使う。
規約：標的列の構造単射や Ω 条件は不要。使われ方：符号補正の全 Hom 上の同型性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 一般の Kan 列の段ごとの π 同型を、元の点つき全 Hom の後合成へ移す。 -/
lemma pointedPost_levelwise_piIsomorphism (A : OmegaSpectrum.{u}) {X Y : KanSequence.{u}}
    (f : KanSequence.Hom X Y) (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedPost A f).right := by
  let u := KanSequence.mappingPathComparison f
  let r := KanSequence.mappingPathSource f
  let p := KanSequence.mappingPathTarget f
  have hr : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedPost A r).right :=
    post_piIsomorphism A r (KanSequence.mappingPathSource_rlp f)
  have hu : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedPost A u).right := by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := (pointedPost A r).right) _ hr
    rw [← Under.comp_right,
      pointedPost_comp_id A u r (KanSequence.mappingPathComparison_source f)]
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _
  have hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedPost A p).right :=
    post_piIsomorphism A p (fun n =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism (f.app n) (hf n))
  have h := hu.comp hp
  rw [← Under.comp_right,
    pointedPost_comp_eq A u p f (KanSequence.mappingPathComparison_target f)] at h
  exact h

end SerrePositivity.KST.Spectra.RawSpectrumMapping
