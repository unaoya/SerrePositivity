module

public import SerrePositivity.KST.Spectra.KanLoopExchangeSign
public import SerrePositivity.KST.Spectra.KanLoopLift

/-!
概要：Ω 条件を持つ Kan 複体で二つの円の交換の符号を計算する。
方針：Kan loop への π_* 同型に沿って写像空間の成分の等式を反映する。
規約：Ω 条件は全基点の実証済みの π_* 同型として与える。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。スペクトルの随伴構造射の符号の調整。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan loop へ π_* 同型で写る対象では二つの Kan 円の交換は内側の円の符号反転と同じ成分の作用。
方針：二重の後合成が成分で単射であることを使い、loop 値での符号の式へ戻す。
規約：h の同型性は全基点・零次数を含む。
使われ方：Goerss–Jardine I §7、BF 1978 §2。Ω スペクトルの各段の二変数の符号。 -/
theorem delooped_exchange_sign {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right]
    (h : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
    (hh : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism h.right) :
    mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Y).hom.right =
      mapπ₀ (PointedObject.basedHomMap CirclePower.space.{u}
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Y)).right := by
  let K : PointedSimplicialSet.{u} := CirclePower.space.{u}
  let L : PointedSimplicialSet.{u} := PointedObject.basedHom K Z
  let A : PointedSimplicialSet.{u} := PointedObject.basedHom K (PointedObject.basedHom K Y)
  let B : PointedSimplicialSet.{u} := PointedObject.basedHom K (PointedObject.basedHom K L)
  let q : A ⟶ B := PointedObject.basedHomMap K
    (PointedObject.basedHomMap K (Y := Y) (Z := L) h)
  have hq₁ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (PointedObject.basedHomMap K h).right :=
    PointedMapping.post_piIsomorphism K h hh
  have hq : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism q.right :=
    PointedMapping.post_piIsomorphism K (PointedObject.basedHomMap K h) hq₁
  have hinj : Function.Injective (mapπ₀ q.right) :=
    (hq.piZero_bijective_at (PointedSimplicialSet.basepoint A)).injective
  have hs := congrArg Under.Hom.right
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post (C := PointedSimplicialSet.{u}) K K h)
  change q.right ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K K L).hom.right =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K K Y).hom.right ≫ q.right at hs
  have ht := ((MonoidalClosed.pre (CirclePower.integerPowerMap.{u} (-1))).naturality h).symm
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at ht
  change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Y ≫
      PointedObject.basedHomMap K (Y := Y) (Z := L) h =
    PointedObject.basedHomMap K (Y := Y) (Z := L) h ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) L at ht
  have hv := congrArg ((ihom K).map) ht
  simp only [Functor.map_comp] at hv
  change PointedObject.basedHomMap K
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Y) ≫ q =
    q ≫ PointedObject.basedHomMap K
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) L) at hv
  funext a
  apply hinj
  have hsπ := congrArg (fun k => mapπ₀ k a) hs
  have hvπ := congrArg (fun k => mapπ₀ k.right a) hv
  simp only [Under.comp_right, mapπ₀_comp_apply] at hsπ hvπ
  exact hsπ.symm.trans ((congrFun (kanLoop_exchange_sign Z) (mapπ₀ q.right a)).trans hvπ.symm)

/-- 概要：通常の円による Ω 条件から二つの Kan 円の交換の符号が従う。
方針：Ω 条件の射を Kan 円へ持ち上げ、その π_* 同型性を使う。
規約：Ω 条件の射は厳密同型でなくてよい。
使われ方：BF 1978 §2、HA §1.4.2。承認済みの Ω スペクトルの各段への適用。 -/
theorem omega_exchange_sign {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) :
    mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Y).hom.right =
      mapπ₀ (PointedObject.basedHomMap CirclePower.space.{u}
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Y)).right :=
  delooped_exchange_sign (kanLoopLift a) (kanLoopLift_piIsomorphism a ha)

end

end SerrePositivity.KST.Spectra
