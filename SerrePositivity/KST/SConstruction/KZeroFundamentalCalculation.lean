module
public import SerrePositivity.KST.SConstruction.KZeroFundamentalGroup
public import SerrePositivity.KST.SConstruction.SOneObjectClasses
public import SerrePositivity.KST.Spectra.LoopHomotopyNaturality
public import SerrePositivity.KST.Spectra.LoopZeroOrientation

/-! # 零次 K 群の基本群表示と元の対象 loop の向き
概要：実際の零次 K 群から基本群への群同型を元の loop の成分で計算する。
方針：元の零段の随伴の恒等性と置換射影の構造可換式を使い、零 loop の自然性へ移す。
規約：通常の円の成分表示との差は逆元として残す。使われ方：S₂ の三辺からの cofiber 加法関係。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open scoped Simplicial

/-- 単射置換の零段の随伴を一段の射影の loop へ写すと元の恒等随伴を回収する。 -/
lemma monicKZeroAdjoint_projection (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ ((monicKKanSequence X).sigma 0) ≫
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
        ((monicKKanSequenceProjection X).app 1) = 𝟙 (boundaryKSpaceFunctor.obj X) := by
  have hc := (monicKKanSequenceProjection X).adjoint_comm 0
  rw [kKanSequence_zero_adjoint] at hc
  have h0 : (monicKKanSequenceProjection X).app 0 ≫
      𝟙 (boundaryKSpaceFunctor.obj X) = 𝟙 (boundaryKSpaceFunctor.obj X) := by
    change (𝟙 (boundaryKSpaceFunctor.obj X)) ≫ 𝟙 _ = 𝟙 _
    exact Category.comp_id _
  exact hc.symm.trans h0

/-- 零段の基本群表示は、元の一重 S の零 loop 同値で計算できる。 -/
lemma kZeroLevelFundamentalGroupEquiv_apply (X : StableModel.{u})
    (a : OmegaSpectrum.levelHomotopy (kOmegaSpectrum X) 0 0) :
    kZeroLevelFundamentalGroupEquiv X a =
      loopZeroHomotopyEquiv ((boundaryKanRealizationFunctor 0).obj X) a := by
  let A := ((monicKKanSequence X).level 1).space
  let B := (boundaryKanRealizationFunctor 0).obj X
  let p := (monicKKanSequenceProjection X).app 1
  let k := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ ((monicKKanSequence X).sigma 0)
  let l := PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p
  have hc : k ≫ l = 𝟙 (boundaryKSpaceFunctor.obj X) := monicKZeroAdjoint_projection X
  have hh : pointedHomotopyMap 0 l (pointedHomotopyMap 0 k a) = a := by
    rw [← pointedHomotopyMap_comp, hc]
    exact pointedHomotopyMap_id _ 0 a
  have hn := loopHomotopyEquiv_natural p 0 (pointedHomotopyMap 0 k a)
  change loopZeroHomotopyEquiv B (pointedHomotopyMap 0 l (pointedHomotopyMap 0 k a)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
      (loopZeroHomotopyEquiv A (pointedHomotopyMap 0 k a)) at hn
  rw [hh] at hn
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism 0 p.right
    (monicKKanSequenceProjection_piIsomorphism X 1) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
      (loopZeroHomotopyEquiv A (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism 0 k.right
        (monicKKanSequence_omegaCondition X 0) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint k) a)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism_apply]
  exact hn.symm

/-- 実際の整数零次 K 群の基本群表示は元の零段表示と零 loop 同値の合成。 -/
lemma kZeroFundamentalGroupEquiv_apply (X : StableModel.{u})
    (a : OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0) :
    kZeroFundamentalGroupEquiv X a =
      loopZeroHomotopyEquiv ((boundaryKanRealizationFunctor 0).obj X)
        (kOmegaSpectrum_zeroGroupEquiv X a) :=
  kZeroLevelFundamentalGroupEquiv_apply X (kOmegaSpectrum_zeroGroupEquiv X a)

/-- 元の自然な π₀ 表示は零段の群同型と通常の連結成分表示の合成。 -/
lemma kHomotopyZeroPiZeroEquiv_formula (X : StableModel.{u})
    (a : OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0) :
    kHomotopyZeroPiZeroEquiv X a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (kOmegaSpectrum_zeroGroupEquiv X a) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
    (pointedHomotopyMap 0 (𝟙 (boundaryKSpaceFunctor.obj X))
      (kOmegaSpectrum_zeroGroupEquiv X a)) = _
  rw [pointedHomotopyMap_id]
  rfl

/-- 元の対象の基本群での K 類は元の円の成分表示の逆元である。 -/
lemma kZeroFundamentalGroupEquiv_objectKClass (X : StableModel.{u}) (x : X.carrier _⦋0⦌) :
    kZeroFundamentalGroupEquiv X (Additive.toMul (objectKClass X x)) =
      (SphereSimplex.componentEquiv ((boundaryKanRealizationFunctor 0).obj X) 0
        (objectKPiZeroClass X x))⁻¹ := by
  rw [kZeroFundamentalGroupEquiv_apply, loopZeroHomotopyEquiv_eq_inv_component]
  have h := (kHomotopyZeroPiZeroEquiv_formula X
    (Additive.toMul (objectKClass X x))).symm.trans (objectKClass_piZero X x)
  exact congrArg (fun a : SSet.π₀ (boundaryKSpaceFunctor.obj X).right =>
    (SphereSimplex.componentEquiv ((boundaryKanRealizationFunctor 0).obj X) 0 a)⁻¹) h

end SerrePositivity.KST.SConstruction
