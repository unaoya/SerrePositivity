module

public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverModelStages

/-!
概要：元の係数環での p の零化を、同じ v 被覆模型の両端の環へ送る。
方針：既存の同じ係数の代数構造の algebraMap を適用する。
規約：模型の有限段の取り替えや強い標数仮定は追加しない。
使われ方：有限型 F_p 模型の全ての段の Frobenius 図式（計画 E15）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u

/-- 同じ v 被覆模型の両端で、元の係数環の p は零になる。 -/
theorem coefficientVCoverModel_primeCast
    (k : Type u) [CommRing k] [IsNoetherianRing k]
    {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (g : R →ₐ[k] S) (p : ℕ) (hK : (p : k) = 0)
    (j : CoefficientVCoverModelIndex k g) :
    (p : ((coefficientVCoverModelSmallArrowDiagram k g).obj j).left) = 0 ∧
      (p : ((coefficientVCoverModelSmallArrowDiagram k g).obj j).right) = 0 := by
  constructor
  · simpa only [map_natCast, map_zero] using congrArg
      (algebraMap k ((coefficientVCoverModelSmallArrowDiagram k g).obj j).left) hK
  · simpa only [map_natCast, map_zero] using congrArg
      (algebraMap k ((coefficientVCoverModelSmallArrowDiagram k g).obj j).right) hK

end SerrePositivity.AlgebraicGeometry
