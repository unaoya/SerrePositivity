module
public import SerrePositivity.KST.Fibration.ZeroMiddleReconstructedFamily

/-!
概要：指定長 Hom 全族の直接 path 評価を、再構成上側の実共有対角へ厳密接続する。
方針：同じ全族切断式で実入力へ戻し、採用済みの全一単体回収式を使う。
規約：Ind-S (9) の強化命題に条件付き。パラメータ頂点の一致で代用しない。
使われ方：K-6 c4 の動く共有対角と上下二胞体の貼り合わせ。
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
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
  (K : SSet.{u + 1}) (h9 : zeroMiddleControlledTriangleSupply.{u})
  (ℓ : (zeroMiddleFullSReconstructionLongSpace s hZ K) _⦋0⦌)

/-- 概要：元の実長 Hom 入力の直接 path 上の全パラメータ評価。
方針：同じ元入力の全族を読み、直接 path の指定頂点で評価する。
規約：元入力に対する実写像であり、新しい Hom 族を選ばない。
使われ方：再構成上側と元の下側が共有する実対角族の照合。 -/
def zeroMiddleReconstructedDirectFamily :
    K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩))) :=
  let P := CategoryTheory.SimplicialThickening.Path
    (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)
  let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve P)
  let H := (SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
      (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)))
  let direct : P :=
    { I := {ULift.up 0, ULift.up 2}
      left := by simp
      right := by simp
      left_le := fun k _ => Fin.zero_le k.down
      le_right := fun k _ => Fin.le_last k.down }
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K ((ihom Pu).obj H)).symm ℓ.val ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ direct))

/-- 概要：再構成上側の共有対角は同じ指定実長 Hom 全族の直接 path 像そのもの。
方針：読出しの全族回収と encode/read の厳密切断式を合成する。
規約：Δ[1] ⊗ K 上の実写像の等式。指定点だけの同型ではない。
使われ方：K=Δ[1] の動く共有対角を全時刻で回収する。 -/
theorem zeroMiddleReconstructedFamily_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ zeroMiddleReconstructedFamily s hZ K h9 ℓ =
      (Δ[1] ◁ zeroMiddleReconstructedDirectFamily s hZ K ℓ) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
          (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
          (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩))) := by
  have h := zeroMiddleFullSReconstructionRead_diagonal s hZ K h9
    (zeroMiddleReconstructedFamilyPoint s hZ K h9 ℓ)
  dsimp only [zeroMiddleFullSReconstructionDiagonalRecovery] at h
  simp only [zeroMiddleReconstructedFamilyPoint_read] at h
  simpa only [zeroMiddleReconstructedFamily, zeroMiddleReconstructedDirectFamily,
    zeroMiddleReconstructedFamilyPoint] using h

end SerrePositivity.KST.Fibration
