module

public import SerrePositivity.KST.Spectra.CircleSmashLoopSwap
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor
public import SerrePositivity.KST.Spectra.DoubleCircleRestrictionNaturality

/-!
概要：反復内部 Hom の二つの円の交換と loop 値の符号反転の比較。
方針：smash の写像を反復 curry し、Kan 円への制限の同型で戻す。
規約：loop 値の標的は円の Kan 置換からの内部 Hom。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。スペクトルの随伴構造射の符号。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：通常の二つの円の反復内部 Hom の交換は loop 値の符号反転の後合成と成分で一致。
方針：反復 curry の交換と後合成の自然性を smash の写像空間の比較へ合成する。
規約：標的の loop は Kan 円からの内部 Hom。
使われ方：Goerss–Jardine I §7、HA §1.4.2。通常の二重円での交換の計算。 -/
theorem ordinaryDoubleCircleLoop_exchange (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u}
      PointedSimplicialSet.circle.{u} (PointedObject.basedHom CirclePower.space.{u} Z)).hom.right =
    mapπ₀ (PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Z))).right := by
  let L : PointedSimplicialSet.{u} := PointedObject.basedHom CirclePower.space.{u} Z
  let v : L ⟶ L := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Z
  let i := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u}
    PointedSimplicialSet.circle.{u} L
  have hs := congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_swap
    (C := PointedSimplicialSet.{u}) PointedSimplicialSet.circle.{u}
      PointedSimplicialSet.circle.{u} L)
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, Under.comp_right] at hs
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedObject.smashSwap PointedSimplicialSet.circle.{u}
    PointedSimplicialSet.circle.{u}) L ≫ i.hom.right =
      i.hom.right ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u}
        PointedSimplicialSet.circle.{u} L).hom.right at hs
  have hv := congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.natural_post
    (C := PointedSimplicialSet.{u}) PointedSimplicialSet.circle.{u}
      PointedSimplicialSet.circle.{u} v)
  change (PointedObject.basedHomMap circleSmashSquare.{u} v).right ≫ i.hom.right =
    i.hom.right ≫ (PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} v)).right at hv
  funext a
  let b := mapπ₀ i.inv.right a
  have hb : mapπ₀ i.hom.right b = a := by
    have hi := congrArg Under.Hom.right i.inv_hom_id
    change i.inv.right ≫ i.hom.right = 𝟙 _ at hi
    rw [← mapπ₀_comp_apply, hi, mapπ₀_id_apply]
  have hsπ := congrArg (fun k => mapπ₀ k b) hs
  have hvπ := congrArg (fun k => mapπ₀ k b) hv
  simp only [mapπ₀_comp_apply, hb] at hsπ hvπ
  exact hsπ.symm.trans ((congrArg (mapπ₀ i.hom.right)
    (congrFun (circleSmashLoop_swap_components Z) b)).trans hvπ)

/-- 概要：二つの Kan 円の反復内部 Hom の交換は loop 値の符号反転と成分で一致。
方針：二変数の円の制限が成分で単射であることを使い、通常の円の比較へ戻す。
規約：源の制限は実証済みの全基点 π_* 同型。
使われ方：Goerss–Jardine I §7、BF 1978 §2。スペクトルの段で用いる Kan 円の交換の符号。 -/
theorem kanDoubleCircleLoop_exchange (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u}
      (PointedObject.basedHom CirclePower.space.{u} Z)).hom.right =
    mapπ₀ (PointedObject.basedHomMap CirclePower.space.{u}
      (PointedObject.basedHomMap CirclePower.space.{u}
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Z))).right := by
  let L : PointedSimplicialSet.{u} := PointedObject.basedHom CirclePower.space.{u} Z
  let v : L ⟶ L := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Z
  let A := PointedObject.basedHom CirclePower.space.{u}
    (PointedObject.basedHom CirclePower.space.{u} L)
  let r := doubleCircleRestriction L
  have hinj : Function.Injective (mapπ₀ r.right) :=
    ((doubleCircleRestriction_piIsomorphism L).piZero_bijective_at
      (PointedSimplicialSet.basepoint A)).injective
  funext a
  apply hinj
  have hs := congrArg (fun k => mapπ₀ k.right a) (doubleCircleRestriction_exchange L)
  have hv := congrArg (fun k => mapπ₀ k.right a) (doubleCircleRestriction_post v)
  simp only [Under.comp_right, mapπ₀_comp_apply] at hs hv
  exact hs.trans ((congrFun (ordinaryDoubleCircleLoop_exchange Z) (mapπ₀ r.right a)).trans hv.symm)

end

end SerrePositivity.KST.Spectra
