module

public import SerrePositivity.KST.Spectra.CircleMappingComponents
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality
public import Mathlib.Algebra.Group.TransferInstance

/-!
概要：円の Kan 置換からの内部 Hom を値とする写像のホモトピー類の群。
方針：内部 Hom の交換で基本群へ移し、その実証済みの群構造を運ぶ。
規約：π₀ 一般には群構造を追加せず、専用の型を使う。
使われ方：Goerss–Jardine I §7、HA §1.4.2。有理化の乗法射と高次群の作用の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：円の Kan 置換の内部 Hom を値とする点つき写像の成分の型。
方針：実際の写像空間の π₀ を専用の型に包む。
規約：対象そのものの ∞ 普遍性は主張しない。
使われ方：Goerss–Jardine I §7、HA §1.4.2。loop を値とするホモトピー類の群。 -/
def LoopMappingClasses (A Y : PointedSimplicialSet.{u}) : Type u :=
  π₀ (PointedObject.basedHom A (PointedObject.basedHom CirclePower.space.{u} Y)).right

namespace LoopMappingClasses

/-- 概要：loop を値とする写像の成分を、写像空間の基本群へ移す同値。
方針：二つの源の交換同型と円の Kan 置換の成分比較を合成する。
規約：Y は Kan、A は任意。
使われ方：Goerss–Jardine I §7、HA §1.4.2。ホモトピー類の群構造の実構成。 -/
def classEquiv (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    LoopMappingClasses A Y ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom A Y).right 0
      (PointedSimplicialSet.basepoint (PointedObject.basedHom A Y)) := by
  letI : KanComplex (PointedSimplicialSet.forget.obj
      (PointedObject.basedHom A (PointedObject.basedHom CirclePower.space.{u} Y))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex A (PointedObject.basedHom CirclePower.space Y)
  let e : (PointedObject.basedHom A (PointedObject.basedHom CirclePower.space.{u} Y)).right ≅
      (PointedObject.basedHom CirclePower.space (PointedObject.basedHom A Y)).right :=
    PointedSimplicialSet.forget.mapIso (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A CirclePower.space Y)
  have hπ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e).piZero_bijective_at
    (PointedSimplicialSet.basepoint
      (PointedObject.basedHom A (PointedObject.basedHom CirclePower.space Y)))
  exact (Equiv.ofBijective (mapπ₀ e.hom) hπ).trans
    (CirclePower.componentEquiv (PointedObject.basedHom A Y))

/-- 概要：loop を値とするホモトピー類は群をなす。
方針：実際の基本群との同値に沿って群演算を運ぶ。
規約：この専用型のみにインスタンスを置く。
使われ方：Goerss–Jardine I §7、HA §1.4.2。写像のパラメータを保つ群演算。 -/
instance group (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    Group (LoopMappingClasses A Y) := (classEquiv A Y).group

/-- 概要：loop を値とするホモトピー類と基本群の群同型。
方針：運んだ群構造の標準的な乗法同型を使う。
規約：順写像は classEquiv と同じ。
使われ方：Goerss–Jardine I §7、HA §1.4.2。冪と群演算の比較。 -/
def groupEquiv (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    LoopMappingClasses A Y ≃* _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom A Y).right 0
      (PointedSimplicialSet.basepoint (PointedObject.basedHom A Y)) :=
  (classEquiv A Y).mulEquiv

/-- 概要：loop の類を基本群へ移す同値はパラメータ源の制限に関して自然。
方針：内部 Hom の交換の制限自然性を π₀ へ送り、円の成分比較の自然性へ合成する。
規約：i は任意の点つき射。
使われ方：Goerss–Jardine I §7、HA §1.4.2。ホモトピー類の群演算の源の自然性。 -/
theorem classEquiv_pre {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (a : LoopMappingClasses B Y) :
    classEquiv A Y
      (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (PointedObject.basedHom CirclePower.space Y)).right a) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) (classEquiv B Y a) := by
  let eA : PointedObject.basedHom A (PointedObject.basedHom CirclePower.space.{u} Y) ≅
      PointedObject.basedHom CirclePower.space (PointedObject.basedHom A Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A CirclePower.space Y
  let eB : PointedObject.basedHom B (PointedObject.basedHom CirclePower.space.{u} Y) ≅
      PointedObject.basedHom CirclePower.space (PointedObject.basedHom B Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso B CirclePower.space Y
  have hs := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality.natural_pre_left
    (C := PointedSimplicialSet.{u}) i CirclePower.space.{u} Y
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hs
  change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (PointedObject.basedHom CirclePower.space Y) ≫ eA.hom =
    eB.hom ≫ PointedObject.basedHomMap CirclePower.space
      (Y := PointedObject.basedHom B Y) (Z := PointedObject.basedHom A Y)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y) at hs
  have hπ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (PointedObject.basedHom CirclePower.space Y)).right
    (PointedObject.basedHomMap CirclePower.space (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y)).right
    eB.hom.right eA.hom.right (congrArg Under.Hom.right hs) a
  change CirclePower.componentEquiv (PointedObject.basedHom A Y)
      (mapπ₀ eA.hom.right
        (mapπ₀
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (PointedObject.basedHom CirclePower.space Y)).right a)) = _
  rw [hπ, CirclePower.componentEquiv_natural]
  rfl


/-- 概要：運んだ群同型の順写像を集合の同値として計算する。
方針：移送した群構造の定義を開く。
規約：A は任意、Y は Kan。
使われ方：Goerss–Jardine I §7。パラメータ制限の群準同型の検証。 -/
@[simp]
theorem groupEquiv_apply (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (a : LoopMappingClasses A Y) : groupEquiv A Y a = classEquiv A Y a := rfl

/-- 概要：パラメータ源の制限は loop を値とするホモトピー類の群準同型。
方針：自然な基本群との比較を通して単位元と積の保存を検査する。
規約：i は任意の点つき射。
使われ方：Goerss–Jardine I §7、HA §1.4.2。写像のホモトピー類の群の反変性。 -/
def preHom {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    LoopMappingClasses B Y →* LoopMappingClasses A Y where
  toFun := mapπ₀
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (PointedObject.basedHom CirclePower.space Y)).right
  map_one' := by
    apply (groupEquiv A Y).injective
    simp only [map_one, groupEquiv_apply, classEquiv_pre]
    rw [← groupEquiv_apply, map_one, map_one]
  map_mul' a b := by
    apply (groupEquiv A Y).injective
    simp only [map_mul, groupEquiv_apply, classEquiv_pre]
    rw [← groupEquiv_apply, map_mul, map_mul]
    rfl

/-- 概要：実際の loop 値の点つき射をそのホモトピー類へ送る。
方針：写像空間の対応する頂点の成分を取る。
規約：Y の Kan 性は定義に不要。
使われ方：Goerss–Jardine I §7。ホモトピー類の演算の代表となる射の選択。 -/
def classOf {A Y : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y) : LoopMappingClasses A Y :=
  π₀.mk (PointedMapping.familyVertex f)

/-- 概要：loop 値のホモトピー類には実際の点つき射の代表がある。
方針：成分の代表頂点と頂点から点つき射への同値を取る。
規約：Kan 性を要求しない。
使われ方：Goerss–Jardine I §7。群演算を表す実際の射の構成。 -/
theorem classOf_surjective (A Y : PointedSimplicialSet.{u}) :
    Function.Surjective (classOf (A := A) (Y := Y)) := by
  intro a
  obtain ⟨v, rfl⟩ := π₀.mk_surjective a
  obtain ⟨f, rfl⟩ :=
    (PointedMapping.familyVertexEquiv A (PointedObject.basedHom CirclePower.space Y)).surjective v
  exact ⟨f, rfl⟩

/-- 概要：実際の射の類のパラメータ制限は前合成の類。
方針：写像空間の頂点の制限を計算する。
規約：Y は Kan、i は任意。
使われ方：Goerss–Jardine I §7。演算の代表の軸への制限。 -/
@[simp]
theorem preHom_classOf {A B Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (i : A ⟶ B) (f : B ⟶ PointedObject.basedHom CirclePower.space.{u} Y) :
    preHom i Y (classOf f) = classOf (i ≫ f) := by
  change mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (PointedObject.basedHom CirclePower.space Y)).right
    (π₀.mk (PointedMapping.familyVertex f)) = _
  rw [mapπ₀_mk, PointedMapping.familyVertex_pre]
  rfl

end LoopMappingClasses

end

end SerrePositivity.KST.Spectra
