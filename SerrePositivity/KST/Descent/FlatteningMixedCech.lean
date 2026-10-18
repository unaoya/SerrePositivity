module

public import SerrePositivity.KST.Descent.AffineBlowupRank
public import SerrePositivity.KST.Descent.MixedCechRefinement

/-!
# 実際の平坦化細分から混合 Čech の分裂行へ

## 概要
アフィン平坦化で構成した正の定 rank の有限忠実平坦細分に、元の被覆の混合 Čech の分裂を付ける。

## 方針
実際の細分射とその可換式を一般の混合 Čech 分裂の構成へ入れる。

## 規約
平坦化中心・低次元性・有限平坦細分・行の分裂の存在を追加の仮定にしない。
値域の Tot による降下の結論は別工程。

## 使われ方
論文 補題 3.3 の平坦化から補題 3.2 の Čech 計算と中心上の帰納へ移る実際の幾何入力。
原典の τ 位相の細分を混合 Čech・分裂降下・Fubini に置換する。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

/-- 概要：実際の有限平坦細分と低次元中心に、元の被覆の混合 Čech の分裂行を供給（補題 3.3）。
方針：構成済みの平坦化細分の同じ a・可換式を、各行の切断と extra degeneracy に使う。
規約：同じ有限型の圏内の二つの異なる被覆を扱い、Tot の降下は主張しない。
使われ方：中心上の次元帰納と有限平坦 transfer を使う二方向の Čech 計算の共通の入力。 -/
theorem exists_affine_flat_refinement_with_split_mixed_rows
    {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S}
    (f : X ⟶ Y) [IsFinite f.hom.left] [Surjective f.hom.left]
    [IsAffine Y.obj.left] [IsIntegral Y.obj.left]
    (d : ℕ) (bound : topologicalKrullDim Y.obj.left ≤ d) :
    ∃ J : Y.obj.left.IdealSheafData, J.support ≠ ⊤ ∧
      topologicalKrullDim (finiteTypeBlowupSquare Y J).square.X₃.obj.left < d ∧
      ∃ (T : FiniteTypeSchemes S) (p : T ⟶ finiteTypeBlowup Y J)
        (a : T ⟶ finiteTypePullback f (finiteTypeBlowupProjection Y J)) (rank : ℕ),
        IsFinite p.hom.left ∧ AlgebraicGeometry.Flat p.hom.left ∧ Surjective p.hom.left ∧
        LocallyOfFinitePresentation p.hom.left ∧ 0 < rank ∧
        (∀ y, p.hom.left.finrank y = rank) ∧
        a ≫ finiteTypePullbackSnd f (finiteTypeBlowupProjection Y J) = p ∧
        ∀ n : SimplexCategoryᵒᵖ, Nonempty (SimplicialObject.Augmented.ExtraDegeneracy
          ((mixedAugmentedCech
            (finiteTypePullbackSnd f (finiteTypeBlowupProjection Y J)) p).obj n)) := by
  obtain ⟨J, hproper, hdim, T, p, a, rank, hpfin, hpflat, hpsurj, hpfp, hpos, hrank, ha⟩ :=
    exists_affine_flat_refinement_with_rank_and_dimension f d bound
  refine ⟨J, hproper, hdim, T, p, a, rank, hpfin, hpflat, hpsurj, hpfp, hpos, hrank, ha, ?_⟩
  intro n
  exact ⟨mixedCechRefinementStageExtraDegeneracy p
    (finiteTypePullbackSnd f (finiteTypeBlowupProjection Y J)) a ha n⟩

end SerrePositivity.KST.Descent
