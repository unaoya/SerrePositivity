module
public import SerrePositivity.HomotopicalAlgebra.Simplicial.GeneratedLeftClass

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorialFactorizationClasses
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryClasses
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement

/-!
概要：余単体単体集合の horn による関手的 Reedy 因子分解。
方針：次数ごとの一般の因子分解構成へ horn の小対象論法を渡す。
規約：Kan–Quillen モデル構造は仮定せず、anodyne と horn の右持ち上げ性だけを使う。
使われ方：Goerss–Jardine VII §4、HTT A.3.3。通常の Tot に用いる Reedy 置換の入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.CosimplicialHornFactorization

noncomputable section

/-- 概要：horn の小対象論法は anodyne と horn RLP の弱因子分解系を与える。
方針：Mathlib の anodyne の生成定理へ帰着する。
規約：モデル圏の弱同値類は使わない。
使われ方：Goerss–Jardine VII §4。matching と latching への持ち上げ性の移送。 -/
lemma hornWeakFactorization : MorphismProperty.IsWeakFactorizationSystem
    SSet.anodyneExtensions.{u} SSet.modelCategoryQuillen.J.{u}.rlp := by
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  infer_instance

/-- 概要：余単体図式の実際の関手的 Reedy 因子分解。
方針：各自然数に一つの対象を持つ simplex 圏の次数帰納を使う。
規約：左は相対 latching anodyne、右は相対 matching horn RLP。
使われ方：HTT A.3.3、Goerss–Jardine VII §4。Reedy fibrant 置換の構成。 -/
abbrev factorization : MorphismProperty.FunctorialFactorizationData
    (reedyLeft simplex SSet.anodyneExtensions.{u})
    (reedyRight simplex SSet.modelCategoryQuillen.J.{u}.rlp) :=
  FunctorFactorizationSequence.functorialFactorizationData simplex
    (fun _ _ h ↦ SimplexCategory.ext h) (fun n ↦ ⟨SimplexCategory.mk n, rfl⟩)
    SerrePositivity.SimplicialModel.AnodyneKanReplacement.factorization

/-- 概要：Reedy horn RLP な自然変換は各段でも horn RLP。
方針：matching への射の右類閉性と引き戻しを使う。
規約：対象ごとの Kan 性は仮定しない。
使われ方：Goerss–Jardine VII §4。置換の各値の Kan 性。 -/
lemma right_app {F G : CosimplicialObject SSet.{u}} (τ : F ⟶ G)
    (hτ : reedyRight simplex SSet.modelCategoryQuillen.J.{u}.rlp τ)
    (j : SimplexCategory) : SSet.modelCategoryQuillen.J.rlp (τ.app j) := by
  let := hornWeakFactorization.{u}
  have hM := matchingEvaluation_mem_right simplex j τ SSet.anodyneExtensions
    SSet.modelCategoryQuillen.J.rlp (fun g ↦ hτ g.obj.right)
  have hp := SSet.modelCategoryQuillen.J.rlp.pullback_fst
    ((matchingComparison simplex j).app G) ((matchingEvaluation simplex j).map τ) hM
  exact (relativeMatchingMap_fst simplex j τ) ▸
    SSet.modelCategoryQuillen.J.rlp.comp_mem _ _ (hτ j) hp

/-- 概要：Reedy anodyne な自然変換は各段でも anodyne。
方針：latching への射の左類閉性と押し出しを使う。
規約：左類は horn から生成する実際の anodyne 拡大。
使われ方：Goerss–Jardine VII §4。Reedy 置換の各段のホモトピー不変性。 -/
lemma left_app {F G : CosimplicialObject SSet.{u}} (τ : F ⟶ G)
    (hτ : reedyLeft simplex SSet.anodyneExtensions.{u} τ)
    (j : SimplexCategory) : SSet.anodyneExtensions (τ.app j) := by
  let := hornWeakFactorization.{u}
  have hL := latchingEvaluation_mem_left simplex j τ SSet.anodyneExtensions
    SSet.modelCategoryQuillen.J.rlp (fun g ↦ hτ g.obj.left)
  have hi := SSet.anodyneExtensions.pushout_inr
    ((latchingEvaluation simplex j).map τ) ((latchingComparison simplex j).app F) hL
  exact (inr_relativeLatchingMap simplex j τ) ▸
    SSet.anodyneExtensions.comp_mem _ _ hi (hτ j)

end

end SerrePositivity.KST.Spectra.CosimplicialHornFactorization
