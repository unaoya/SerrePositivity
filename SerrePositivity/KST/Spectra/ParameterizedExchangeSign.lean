module

public import SerrePositivity.KST.Spectra.DeloopedExchangeSign
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomPairExchange
public import SerrePositivity.KST.Spectra.MappingDelooping
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-!
概要：任意のパラメータを持つ二重 loop の交換の符号。
方針：パラメータを標的へ移し、写像空間に移した Ω 条件を適用する。
規約：π₀ の等式の後合成保存を仮定せず、実際の同型で比較する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。随伴構造射のホモトピー可換性。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Ω 条件の標的について任意の源から見た二つの Kan 円の交換は内側の符号反転と成分で一致。
方針：パラメータを内側へ移す同型で Ω 条件を持つ写像空間の交換の式へ戻す。
規約：パラメータ A に Kan 性や有限性を要求しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。各段の随伴構造射の比較に必要な源を保つ符号の式。 -/
theorem omega_exchange_sign_parameterized (A : PointedSimplicialSet.{u})
    {Y Z : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right) :
    mapπ₀ (PointedObject.basedHomMap A
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Y).hom).right =
      mapπ₀ (PointedObject.basedHomMap A (PointedObject.basedHomMap CirclePower.space.{u}
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Y))).right := by
  let K : PointedSimplicialSet.{u} := CirclePower.space.{u}
  let i := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso A K K Y
  have hinj : Function.Injective (mapπ₀ i.hom.right) := by
    intro b c hbc
    have h := congrArg (mapπ₀ i.inv.right) hbc
    have hi := congrArg Under.Hom.right i.hom_inv_id
    change i.hom.right ≫ i.inv.right = 𝟙 _ at hi
    simpa only [← mapπ₀_comp_apply, hi, mapπ₀_id_apply] using h
  have htarget := delooped_exchange_sign (mappingKanDelooping A a)
    (mappingKanDelooping_piIsomorphism A a ha)
  have hs := congrArg Under.Hom.right
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso_swap (C := PointedSimplicialSet.{u}) A K K Y)
  have hv := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.pairIso_pre_inner
    (C := PointedSimplicialSet.{u}) A K (CirclePower.integerPowerMap.{u} (-1)) Y
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hv
  have hv' := congrArg Under.Hom.right hv
  funext b
  apply hinj
  have hsπ := congrArg (fun k => mapπ₀ k b) hs
  have hvπ := congrArg (fun k => mapπ₀ k b) hv'
  simp only [Under.comp_right, mapπ₀_comp_apply] at hsπ hvπ
  exact hsπ.trans ((congrFun htarget (mapπ₀ i.hom.right b)).trans hvπ.symm)

/-- 概要：任意の二重 loop 値の点つき射に対し、円の交換と内側の符号反転は同じ成分を与える。
方針：パラメータ付き写像空間の関数の等式をその射の頂点の成分で評価する。
規約：源 A は任意で、標的 Y に Ω 条件を仮定する。
使われ方：BF 1978 §2、HA §1.4.2。随伴構造射の二回合成に適用する符号の式。 -/
theorem omega_exchange_sign_component {A Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right]
    (a : Y ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
    (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u}
      (PointedObject.basedHom CirclePower.space.{u} Y)) :
    PointedMapping.componentOf
        (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u} Y).hom) =
      PointedMapping.componentOf (f ≫ PointedObject.basedHomMap CirclePower.space.{u}
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Y)) := by
  have h := congrFun (omega_exchange_sign_parameterized A a ha) (PointedMapping.componentOf f)
  simpa only [PointedMapping.componentOf, mapπ₀_mk, PointedMapping.familyVertex_post] using h

end

end SerrePositivity.KST.Spectra
