module

public import SerrePositivity.KST.Spectra.LoopMultiplication
public import SerrePositivity.KST.Spectra.PointedGroupProduct

/-!
概要：円の Kan 置換の次数射の前合成は、loop の正次数の群に冪で作用する。
方針：類の積を表す実際の射の単位則から通常の群の積を計算する。
規約：通常の群構造は RelStruct・MulStruct から構成したものを使う。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。有理 telescope の実際の遷移射。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.LoopMappingClasses

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：等しい loop 値のホモトピー類の射は同じ正次数準同型を誘導する。
方針：成分の等式を基点固定ホモトピーへ戻して不変性を使う。
規約：パラメータ源 A はこの補題では Kan。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。積の単位則の群での計算。 -/
theorem groupMap_eq_of_classOf_eq {A Y : PointedSimplicialSet.{u}}
    [KanComplex A.right] [KanComplex Y.right]
    (f g : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
    (h : classOf f = classOf g) (n : ℕ) : pointedGroupMap n f = pointedGroupMap n g := by
  obtain ⟨H, hH⟩ := (PointedMapping.piZero_eq_iff_pointedHomotopy f g).mp h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_eq_of_basedHomotopy _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedRelativeHomotopy f g H hH)

/-- 概要：loop の積を表す射は正次数の群に通常の積で作用する。
方針：直積への誘導像を二つの軸に分解し、各軸の単位則を使う。
規約：A と Y は Kan、次数は n+1。
使われ方：Goerss–Jardine I §7、HA §1.4.2。反復積の誘導作用。 -/
theorem groupMap_pair_multiplication {A Y : PointedSimplicialSet.{u}}
    [KanComplex A.right] [KanComplex Y.right]
    (f g : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup A.right n A.basepoint) :
    pointedGroupMap n (PointedObject.prodLift f g ≫ multiplication Y) a =
      pointedGroupMap n f a * pointedGroupMap n g a := by
  rw [pointedGroupMap_comp, pointedGroupMap_prodLift, map_mul]
  rw [← pointedGroupMap_comp n (PointedObject.axisLeft _ _) (multiplication Y),
    ← pointedGroupMap_comp n (PointedObject.axisRight _ _) (multiplication Y)]
  rw [groupMap_eq_of_classOf_eq _ _ (classOf_axisLeft_multiplication Y) n,
    groupMap_eq_of_classOf_eq _ _ (classOf_axisRight_multiplication Y) n,
    pointedGroupMap_id, pointedGroupMap_id]

/-- 概要：loop の冪の実際の代表となる自己射。
方針：零射から出発して、恒等射と選んだ積の射による反復積を取る。
規約：単体集合の実際の射を再帰的に構成する。
使われ方：Goerss–Jardine I §7。有理化の次数射の誘導作用の検証。 -/
def powerRepresentative (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    ℕ → (PointedObject.basedHom CirclePower.space.{u} Y ⟶
      PointedObject.basedHom CirclePower.space Y)
  | 0 => 0
  | m + 1 => PointedObject.prodLift (powerRepresentative Y m) (𝟙 _) ≫ multiplication Y

/-- 概要：反復積の射の類は恒等射の類の冪。
方針：類における二変数積の式を帰納的に適用する。
規約：冪は loop 値のホモトピー類の群で取る。
使われ方：Goerss–Jardine I §7。円の次数射とのホモトピー比較。 -/
theorem classOf_powerRepresentative (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (m : ℕ) : classOf (powerRepresentative Y m) = classOf (𝟙 _) ^ m := by
  induction m with
  | zero => exact (classOf_zero _ Y).trans (pow_zero _).symm
  | succ m ih =>
    change classOf (PointedObject.prodLift _ _ ≫ multiplication Y) = _
    rw [classOf_pair_multiplication, ih, pow_succ]

/-- 概要：反復積の射は通常の正次数の群で冪として計算できる。
方針：実際の積の射の群への作用を帰納的に使う。
規約：次数は n+1、基点は定数 loop。
使われ方：Goerss–Jardine I §7。円の次数射の作用の通常の群への移送。 -/
theorem groupMap_powerRepresentative (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (m n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom CirclePower.space.{u} Y).right n
      (PointedSimplicialSet.basepoint (PointedObject.basedHom CirclePower.space Y))) :
    pointedGroupMap n (powerRepresentative Y m) a = a ^ m := by
  induction m with
  | zero => exact (pointedGroupMap_zero _ _ n a).trans (pow_zero _).symm
  | succ m ih =>
    change pointedGroupMap n (PointedObject.prodLift _ _ ≫ multiplication Y) a = _
    rw [groupMap_pair_multiplication, ih, pointedGroupMap_id, pow_succ]

/-- 概要：円の実際の次数射の前合成は通常の正次数ホモトピー群の m 乗。
方針：loop の類で反復積の射と比較し、基点固定ホモトピーの不変性を使う。
規約：通常の群の次数は n+1、m は任意の自然数。
使われ方：Goerss–Jardine I §7、BF 1978 §2。有理化の遷移射の群への実証済み作用。 -/
theorem groupMap_pre_power (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (m n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom CirclePower.space.{u} Y).right n
      (PointedSimplicialSet.basepoint (PointedObject.basedHom CirclePower.space Y))) :
    pointedGroupMap n (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.powerMap m) Y) a = a ^ m := by
  have h := post_power (PointedObject.basedHom CirclePower.space.{u} Y) Y m
    (classOf (𝟙 (PointedObject.basedHom CirclePower.space.{u} Y)))
  change mapπ₀ (PointedObject.basedHomMap
    (PointedObject.basedHom CirclePower.space.{u} Y)
    (Y := PointedObject.basedHom CirclePower.space Y)
    (Z := PointedObject.basedHom CirclePower.space Y)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.powerMap m) Y)).right
    (π₀.mk (PointedMapping.familyVertex
      (𝟙 (PointedObject.basedHom CirclePower.space.{u} Y)))) = _ at h
  rw [mapπ₀_mk, PointedMapping.familyVertex_post, Category.id_comp] at h
  have hc : classOf (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.powerMap m) Y) =
      classOf (powerRepresentative Y m) := h.trans (classOf_powerRepresentative Y m).symm
  rw [groupMap_eq_of_classOf_eq _ _ hc n]
  exact groupMap_powerRepresentative Y m n a

end

end SerrePositivity.KST.Spectra.LoopMappingClasses
