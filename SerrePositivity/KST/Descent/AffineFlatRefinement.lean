module

public import SerrePositivity.KST.Descent.AffineFiniteFlattening
public import SerrePositivity.KST.Descent.BoundaryFlatRefinement

/-!
# 整なアフィン基底への有限全射の実際の有限忠実平坦細分

## 概要
真閉中心の blowup 後に、元の有限全射の底変換を細分する実際の有限忠実平坦被覆を構成する。

## 方針
支配する整成分を選び、実際の平坦化中心と同じ境界での全射性を合成する。

## 規約
平坦化中心や平坦被覆の存在を仮定しない。元の有限型の圏内の射を返す。

## 使われ方
論文 補題 3.3 の幾何入力と、公理 (6) の整なアフィン Noether 基底の場合。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S}
  (f : X ⟶ Y) [IsFinite f.hom.left] [Surjective f.hom.left]
  [IsAffine Y.obj.left] [IsIntegral Y.obj.left]

/-- 概要：整アフィン基底への有限全射は真閉中心の blowup 後に有限忠実平坦な細分を持つ（補題 3.3）。
方針：生成点を支配する整成分を選び、証明済みの平坦化中心・全射性・実際の細分射を組み合わせる。
規約：有限型の圏内の実際の被覆と細分射、中心の真閉性を返す。降下は結論しない。
使われ方：有限忠実平坦 Čech 降下と中心上の低次元帰納への幾何的な還元。 -/
theorem exists_affine_finiteFlat_refinement :
    ∃ (r : Γ(Y.obj.left, ⊤)) (J : Y.obj.left.IdealSheafData), r ≠ 0 ∧
      (∀ W : Y.obj.left.affineOpens, (J.ideal W).FG) ∧
      Y.obj.left.basicOpen r ≤ _root_.SerrePositivity.AlgebraicGeometry.centerComplement J ∧ J.support ≠ ⊤ ∧
      ∃ (T : FiniteTypeSchemes S) (p : T ⟶ finiteTypeBlowup Y J)
        (a : T ⟶ finiteTypePullback f (finiteTypeBlowupProjection Y J)),
        IsFinite p.hom.left ∧ Flat p.hom.left ∧ Surjective p.hom.left ∧
          LocallyOfFinitePresentation p.hom.left ∧
          a ≫ finiteTypePullbackSnd f (finiteTypeBlowupProjection Y J) = p := by
  obtain ⟨c, _, hfinite, hc⟩ := exists_finite_surjective_integralComponent f
  have : IsFinite (integralComponentMap f c).hom.left := hfinite
  obtain ⟨r, J, hr, hfg, hadm, hproper, hflat⟩ :=
    exists_affine_finite_flattening_center (integralComponentMap f c).hom.left
  have := hflat
  obtain ⟨T, p, a, hpfin, hpflat, hpsurj, hpfp, ha⟩ :=
    exists_finiteFlat_cover_refining_boundary f c hc J r
      (mem_nonZeroDivisors_iff_ne_zero.mpr hr)
  exact ⟨r, J, hr, hfg, hadm, hproper, T, p, a, hpfin, hpflat, hpsurj, hpfp, ha⟩

end SerrePositivity.KST.Descent
