module

public import SerrePositivity.KST.Spectra.SphereMappingComponents
public import SerrePositivity.KST.Spectra.CirclePower

/-!
概要：円の Kan 置換からの写像空間の π₀ と基本群、および円の自己射による冪作用。
方針：anodyne 単位による制限と球面の成分比較を合成し、指定基本類の計算を使う。
規約：高次ホモトピー群の作用はまだ主張しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）、BF 1978 §2。有理化の乗法射の作用。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.CirclePower

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：円の Kan 置換からの写像空間の成分と標的の基本群の同値。
方針：anodyne な単位による制限の全単射性と球面の成分比較を合成する。
規約：標的は点つき Kan 複体。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。円の自己射の作用を基本群で検査する。 -/
def componentEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    π₀ (PointedObject.basedHom space.{u} Y).right ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right 0 Y.basepoint := by
  have hpre : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed unit.{u} Y).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp unit
        (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle.{u}) Y)
  exact (Equiv.ofBijective (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed unit Y).right)
    (hpre.piZero_bijective_at
      (PointedSimplicialSet.basepoint (PointedObject.basedHom space Y)))).trans
      (SphereSimplex.componentEquiv Y 0)

/-- 概要：円の成分比較は点つき射の指定基本類の像で計算できる。
方針：単位への制限と sphere の自然な単体表示を使う。
規約：任意の Kan 値の点つき射 f。
使われ方：Kerodon §3.2.3（Tag 00W3）、Goerss–Jardine I §7。写像空間の自己射の計算。 -/
@[simp]
theorem componentEquiv_familyVertex (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (f : space.{u} ⟶ Y) :
    componentEquiv Y (π₀.mk (PointedMapping.familyVertex f)) = evaluateGenerator f := by
  change SphereSimplex.componentClass Y 0
    (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed unit Y).right (π₀.mk (PointedMapping.familyVertex f))) = _
  rw [mapπ₀_mk, PointedMapping.familyVertex_pre, SphereSimplex.componentClass_familyVertex,
    SphereSimplex.equiv_comp]
  rfl

/-- 概要：円の自己射による写像空間の π₀ の作用は、基本群の m 乗。
方針：任意の成分を点つき射で表し、指定基本類の後合成での計算へ還元する。
規約：集合の同値の下で全ての成分に対して計算する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）、BF 1978 §2。有理 telescope の冪作用の零次数。 -/
theorem componentEquiv_pre_power (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (m : ℕ) (a : π₀ (PointedObject.basedHom space.{u} Y).right) :
    componentEquiv Y (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (powerMap m) Y).right a) =
      componentEquiv Y a ^ m := by
  obtain ⟨v, rfl⟩ := π₀.mk_surjective a
  obtain ⟨f, rfl⟩ := (PointedMapping.familyVertexEquiv space Y).surjective v
  change componentEquiv Y (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (powerMap m) Y).right
    (π₀.mk (PointedMapping.familyVertex f))) =
      componentEquiv Y (π₀.mk (PointedMapping.familyVertex f)) ^ m
  rw [mapπ₀_mk, PointedMapping.familyVertex_pre, componentEquiv_familyVertex,
    componentEquiv_familyVertex]
  exact evaluateGenerator_power f m

/-- 概要：円の Kan 置換の成分比較は標的の点つき Kan 射に関して自然。
方針：代表となる射の指定基本類の像を、誘導準同型の合成で計算する。
規約：全ての連結成分に適用する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。パラメータ変数に関する群演算の自然性。 -/
theorem componentEquiv_natural {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z)
    (a : π₀ (PointedObject.basedHom space.{u} Y).right) :
    componentEquiv Z (mapπ₀ (PointedObject.basedHomMap space p).right a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) (componentEquiv Y a) := by
  obtain ⟨v, rfl⟩ := π₀.mk_surjective a
  obtain ⟨f, rfl⟩ := (PointedMapping.familyVertexEquiv space Y).surjective v
  change componentEquiv Z (mapπ₀ (PointedObject.basedHomMap space p).right
    (π₀.mk (PointedMapping.familyVertex f))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
        (componentEquiv Y (π₀.mk (PointedMapping.familyVertex f)))
  rw [mapπ₀_mk, PointedMapping.familyVertex_post, componentEquiv_familyVertex,
    componentEquiv_familyVertex]
  exact DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := 0) f.right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f) p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (f ≫ p))) generator

end

end SerrePositivity.KST.Spectra.CirclePower
