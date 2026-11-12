module

public import SerrePositivity.KST.Spectra.LoopInversion
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySelfComposite
public import SerrePositivity.KST.Spectra.UnbasedHomotopyIsomorphism

/-!
概要：円の整数次数射の全正次数群での作用と符号反転の全基点 π_* 同型性。
方針：類の逆元の代表と比較し、二回の符号反転を恒等射とホモトピーで結ぶ。
規約：全基点の条件は基点固定の群の計算とは別に検証する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。loop と次数移動の比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.LoopMappingClasses

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：loop 値の実際の射の後で円の整数次数射を前合成すると類は整数冪。
方針：パラメータつき成分の作用を実際の射の頂点で計算する。
規約：A は任意、Y は Kan。
使われ方：Goerss–Jardine I §7。二回の符号反転の計算。 -/
theorem classOf_comp_pre_integer {A Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y) (z : ℤ) :
    classOf (f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z) Y) = classOf f ^ z := by
  have h := post_integerPower A Y z (classOf f)
  change mapπ₀ (PointedObject.basedHomMap A
    (Y := PointedObject.basedHom CirclePower.space Y)
    (Z := PointedObject.basedHom CirclePower.space Y)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z) Y)).right
    (π₀.mk (PointedMapping.familyVertex f)) = _ at h
  rw [mapπ₀_mk, PointedMapping.familyVertex_post] at h
  exact h

/-- 概要：円の整数次数射の前合成の類は恒等射の類の整数冪。
方針：実際の射の合成の式で恒等射を使う。
規約：全整数 z。
使われ方：Goerss–Jardine I §7。通常の群の作用と二回の符号反転の比較。 -/
theorem classOf_pre_integer (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (z : ℤ) :
    classOf (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z) Y) =
      classOf (𝟙 (PointedObject.basedHom CirclePower.space.{u} Y)) ^ z := by
  simpa only [Category.id_comp] using
    classOf_comp_pre_integer (𝟙 (PointedObject.basedHom CirclePower.space.{u} Y)) z

/-- 概要：円の整数次数の実際の射の前合成は全正次数群の整数冪。
方針：整数冪を表す実際の射と類で比較し、基点固定ホモトピーの不変性を使う。
規約：群の次数は n+1。
使われ方：Goerss–Jardine I §7、BF 1978 §2。実際の符号反転の群への作用。 -/
theorem groupMap_pre_integer (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (z : ℤ) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom CirclePower.space.{u} Y).right n
      (PointedSimplicialSet.basepoint (PointedObject.basedHom CirclePower.space Y))) :
    pointedGroupMap n (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z) Y) a = a ^ z := by
  have hc : classOf (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z) Y) =
      classOf (integerPowerRepresentative Y z) :=
    (classOf_pre_integer Y z).trans (classOf_integerPowerRepresentative Y z).symm
  rw [groupMap_eq_of_classOf_eq _ _ hc n]
  exact groupMap_integerPowerRepresentative Y z n a

/-- 概要：loop の符号反転の二回合成は恒等射と基点固定でホモトピック。
方針：loop 値の射の類で逆元の二回適用を計算し、実際のホモトピーへ戻す。
規約：Hom の源は円の Kan 置換。
使われ方：Goerss–Jardine I §7、BF 1978 §2。符号反転の全基点での同型性。 -/
theorem pre_neg_one_twice_homotopy (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    ∃ H : SSet.Homotopy
      ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap (-1)) Y) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap (-1)) Y)).right
      (𝟙 (PointedObject.basedHom CirclePower.space.{u} Y).right),
      (PointedObject.basedHom CirclePower.space Y).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          (PointedObject.basedHom CirclePower.space Y).hom := by
  have hc : classOf
      ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap (-1)) Y) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap (-1)) Y)) =
      classOf (𝟙 (PointedObject.basedHom CirclePower.space.{u} Y)) := by
    rw [classOf_comp_pre_integer, classOf_pre_integer]
    simp only [zpow_neg_one, inv_inv]
  exact (PointedMapping.piZero_eq_iff_pointedHomotopy _ _).mp hc

/-- 概要：loop の符号反転は零次数を含む全基点の π_* 同型。
方針：二回合成のホモトピー対合性と自己合成からの検出を使う。
規約：定数 loop の基点に限定しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。符号を変更する Ω 条件の保存。 -/
theorem pre_neg_one_piIsomorphism (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap (-1)) Y).right := by
  obtain ⟨H, _⟩ := pre_neg_one_twice_homotopy Y
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_self_comp
  exact (kanPiIsomorphism_iff_of_homotopy H).mpr (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _)

end

end SerrePositivity.KST.Spectra.LoopMappingClasses
