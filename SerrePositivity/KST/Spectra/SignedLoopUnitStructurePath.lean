module

public import SerrePositivity.KST.Spectra.SignedLoopStructurePaths
public import SerrePositivity.KST.Spectra.PointedBasedPathClosed

/-!
概要：単位と全 Hom の厳密化へ共通に使う、固定した Kan 随伴の構造区間。
方針：単位の段射の空間で一度だけ逆区間を選び、他の源へは内部 Hom の作用で移す。
規約：内部 Hom ごとに区間を選び直さない。使われ方：トレース付き BF 単位の共通境界。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 単位の構造正方形の向きを戻した実区間を、各標的と段で一度だけ選ぶ。 -/
def signedLoopUnitStructurePath (X : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint ((KanSequence.signedLoopTail X.toKanSequence).level (n + 1)).space)
      (X.sigma n ≫ KanSequence.kanAdjoint X.toKanSequence (n + 1))
      (PointedSimplicialSet.circle.{u} ◁ KanSequence.kanAdjoint X.toKanSequence n ≫
        (KanSequence.signedLoopTail X.toKanSequence).sigma n) :=
  PointedMapping.basedPathOfComponent
    (KanSequence.kanAdjoint_signedLoopTail_basedChain X.toKanSequence_omega n).component.symm

end SerrePositivity.KST.Spectra.OmegaSpectrum
