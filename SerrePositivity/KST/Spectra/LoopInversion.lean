module

public import SerrePositivity.KST.Spectra.LoopPositivePower
public import SerrePositivity.KST.Spectra.CircleIntegerComponents

/-!
概要：loop の逆元を表す実際の射と、整数冪の正次数群での計算。
方針：類の逆元の代表を取り、積の単位則を通常のホモトピー群へ移す。
規約：loop の群演算の厳密な群対象性は主張しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。符号反転の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.LoopMappingClasses

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：loop の逆元をホモトピー類で表す実際の自己射。
方針：恒等射の類の逆元の実際の代表を選ぶ。
規約：選択は代表のみに用いる。
使われ方：Goerss–Jardine I §7。loop の符号反転の正次数群での計算。 -/
def inversion (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    PointedObject.basedHom CirclePower.space.{u} Y ⟶ PointedObject.basedHom CirclePower.space Y :=
  Classical.choose (classOf_surjective _ Y
    ((classOf (𝟙 (PointedObject.basedHom CirclePower.space Y)))⁻¹))

/-- 概要：逆元を表す射の類は恒等射の類の逆元。
方針：代表の選択の性質を使う。
規約：ホモトピー類の群での等式。
使われ方：Goerss–Jardine I §7。逆元の射の通常の群への作用の検証。 -/
theorem classOf_inversion (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    classOf (inversion Y) = (classOf (𝟙 (PointedObject.basedHom CirclePower.space.{u} Y)))⁻¹ :=
  Classical.choose_spec (classOf_surjective _ Y _)

/-- 概要：逆元を表す実際の射は正次数群の逆元を誘導する。
方針：恒等射と逆元の射の積が零射とホモトピックであることを通常の群へ移す。
規約：次数は n+1。
使われ方：Goerss–Jardine I §7、HA §1.4.2。負の整数冪の群への作用。 -/
theorem groupMap_inversion (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom CirclePower.space.{u} Y).right n
      (PointedSimplicialSet.basepoint (PointedObject.basedHom CirclePower.space Y))) :
    pointedGroupMap n (inversion Y) a = a⁻¹ := by
  have hc : classOf (PointedObject.prodLift (𝟙 _) (inversion Y) ≫ multiplication Y) =
      classOf (0 : PointedObject.basedHom CirclePower.space.{u} Y ⟶
        PointedObject.basedHom CirclePower.space Y) := by
    rw [classOf_pair_multiplication, classOf_inversion, mul_inv_cancel, classOf_zero]
  have hn := DFunLike.congr_fun (groupMap_eq_of_classOf_eq _ _ hc n) a
  rw [groupMap_pair_multiplication, pointedGroupMap_id, pointedGroupMap_zero] at hn
  apply mul_left_cancel (a := a)
  rw [hn, mul_inv_cancel]

/-- 概要：loop の整数冪を表す実際の自己射。
方針：非負の整数では反復積、負の整数では反復積の後で逆元の射を使う。
規約：整数の二つの標準形で定義する。
使われ方：Goerss–Jardine I §7。円の整数次数射との比較。 -/
def integerPowerRepresentative (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    ℤ → (PointedObject.basedHom CirclePower.space.{u} Y ⟶
      PointedObject.basedHom CirclePower.space Y)
  | Int.ofNat n => powerRepresentative Y n
  | Int.negSucc n => powerRepresentative Y (n + 1) ≫ inversion Y

/-- 概要：整数冪の代表の類は恒等射の類の整数冪。
方針：負の整数ではパラメータ制限準同型に沿って逆元を引き戻す。
規約：全整数 z。
使われ方：Goerss–Jardine I §7。円の実際の整数次数射の識別。 -/
theorem classOf_integerPowerRepresentative (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (z : ℤ) : classOf (integerPowerRepresentative Y z) =
      classOf (𝟙 (PointedObject.basedHom CirclePower.space.{u} Y)) ^ z := by
  cases z with
  | ofNat n =>
    change classOf (powerRepresentative Y n) =
      classOf (𝟙 (PointedObject.basedHom CirclePower.space.{u} Y)) ^ (n : ℤ)
    rw [zpow_natCast]
    exact classOf_powerRepresentative Y n
  | negSucc n =>
    have h := congrArg (preHom (powerRepresentative Y (n + 1)) Y) (classOf_inversion Y)
    rw [preHom_classOf, map_inv, preHom_classOf, Category.comp_id,
      classOf_powerRepresentative] at h
    exact h.trans (zpow_negSucc _ _).symm

/-- 概要：整数冪の代表は通常の正次数群で整数冪を誘導する。
方針：反復積と逆元の誘導作用を合成する。
規約：通常の次数は n+1、z は任意の整数。
使われ方：Goerss–Jardine I §7、HA §1.4.2。負の次数射の通常の群への移送。 -/
theorem groupMap_integerPowerRepresentative (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (z : ℤ) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom CirclePower.space.{u} Y).right n
      (PointedSimplicialSet.basepoint (PointedObject.basedHom CirclePower.space Y))) :
    pointedGroupMap n (integerPowerRepresentative Y z) a = a ^ z := by
  cases z with
  | ofNat m =>
    change pointedGroupMap n (powerRepresentative Y m) a = a ^ (m : ℤ)
    rw [zpow_natCast]
    exact groupMap_powerRepresentative Y m n a
  | negSucc m =>
    change pointedGroupMap n (powerRepresentative Y (m + 1) ≫ inversion Y) a = _
    rw [pointedGroupMap_comp, groupMap_inversion, groupMap_powerRepresentative, zpow_negSucc]

end

end SerrePositivity.KST.Spectra.LoopMappingClasses
