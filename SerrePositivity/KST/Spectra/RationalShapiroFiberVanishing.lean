module

public import SerrePositivity.KST.Spectra.HomotopyFiberVanishing
public import SerrePositivity.KST.Spectra.RationalShapiro

/-!
概要：有限群の有理自明作用の標準比較の実際の homotopy fiber の全整数次数の群は零。
方針：骨格の cohomology 消滅・逐次障害補正・lim¹ 消滅による有理 Shapiro を長完全列へ適用。
規約：π の消滅は構成した BF fiber の群の Subsingleton として述べる。
使われ方：Goerss–Jardine VIII §2、BF 1978 §2。L9e の cohomology 消滅から π 消滅への合流。
-/

@[expose] public section
universe u
namespace SerrePositivity.KST.Spectra
noncomputable section

/-- 有限群の有理標準比較の fiber は、全整数次数のホモトピー群が零。 -/
theorem rational_homotopyFixedPointsUnit_fiberGroup_subsingleton
    (G : Type u) [Group G] [Finite G] (X : OmegaSpectrum.{u}) (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup
      (OmegaSpectrum.homotopyFiber
        (homotopyFixedPointsUnit G (OmegaSpectrum.rationalization X))) j) :=
  OmegaSpectrum.homotopyFiberGroup_subsingleton_of_injective_surjective _ j
    (rational_homotopyFixedPointsUnit_homotopyMap_bijective G X j).injective
    (rational_homotopyFixedPointsUnit_homotopyMap_bijective G X (j + 1)).surjective

end
end SerrePositivity.KST.Spectra
