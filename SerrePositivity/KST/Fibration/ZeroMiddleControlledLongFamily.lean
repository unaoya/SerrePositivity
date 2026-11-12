module
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleLongHomFamily

/-!
概要：元の全 S• 中間頂点と指定長 Hom 入力から、同じ二短辺の実制御二胞体族を構成する。
方針：Ind-S の公開された各長 Hom 全族上の構成を元の上側入力へ代入する。
規約：(9) の厳密切断や正規化対角は使わず、全ホーンと各入力の全 native Hom だけを回収する。
使われ方：K-6 c4 の実構成部分と、供給待ちの全対角比較を分離する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：同じ長 Hom 入力の全 native 値を各入力で保持する実上側族が存在する。
方針：元の二短辺・ホーン・指定合成端の実 fiber 点を Ind-S の構成定理へ渡す。
規約：(9) の存在仮定は不要。全時刻の共有対角の厳密一致はこの定理では主張しない。
使われ方：元の全 S• 上側の実二胞体構成を先に放電する。 -/
theorem zeroMiddleFullSControlledFamily_exists
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
    (K : SSet.{u + 1}) (ℓ : (zeroMiddleFullSReconstructionLongSpace s hZ K) _⦋0⦌) :
    let P := SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)
    let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve P)
    let H := (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)))
    let L := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K ((ihom Pu).obj H)).symm ℓ.val
    ∃ F : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ F = zeroMiddleFullSReconstructionHorn s hZ K ∧
      ∀ k : K _⦋0⦌,
        HEq (L.app (Opposite.op ⦋0⦌) k)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamily_exists_of_longHom
    (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
    (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)) K
    (zeroMiddleFullSFirstFamily s K) (zeroMiddleFullSLastFamily s hZ K)
    (zeroMiddleFullSReconstructionHorn s hZ K)
    (zeroMiddleFullSReconstructionHorn_first s hZ K)
    (zeroMiddleFullSReconstructionHorn_last s hZ K)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ℓ.val) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex _
  have hv := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply ℓ.val
  have hℓ := ℓ.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)
  change (((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _)).app (Opposite.op ⦋0⦌))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ℓ.val)) = _
  exact (congrArg ((((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _)).app (Opposite.op ⦋0⦌))) hv).trans hℓ

end SerrePositivity.KST.Fibration
