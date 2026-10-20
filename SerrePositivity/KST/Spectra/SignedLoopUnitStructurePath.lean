module

public import SerrePositivity.KST.Spectra.SignedLoopTracedStructureInterval
public import SerrePositivity.KST.Spectra.PointedBasedPathClosed

/-!
概要：単位と全 Hom の厳密化へ共通に使う、固定した Kan 随伴の構造区間。
方針：元の二つの符号区間の合成・逆向き三角形を保持し、同じ評価で移す。
規約：成分の等式から区間を選び直さない。使われ方：トレース付き BF 単位の共通境界。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の符号区間と二つの実三角形を保持する、共通の単位構造区間。 -/
def signedLoopUnitStructurePath (X : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint ((KanSequence.signedLoopTail X.toKanSequence).level (n + 1)).space)
      (X.sigma n ≫ KanSequence.kanAdjoint X.toKanSequence (n + 1))
      (PointedSimplicialSet.circle.{u} ◁ KanSequence.kanAdjoint X.toKanSequence n ≫
        (KanSequence.signedLoopTail X.toKanSequence).sigma n) :=
  KanSequence.signedLoopStructureInterval X.toKanSequence X.toKanSequence_omega n

/-- 単位の同じ構造辺は、保存した逆向き区間の元の評価像そのもの。 -/
lemma signedLoopUnitStructurePath_path (X : OmegaSpectrum.{u}) (n : ℕ) :
    (signedLoopUnitStructurePath X n).path =
      (KanSequence.signedLoopStructureReverse X.toKanSequence X.toKanSequence_omega n).path.path ≫
        (PointedMapping.uncurryAction (X.level n).space
          ((KanSequence.signedLoopTail X.toKanSequence).level (n + 1)).space).right :=
  KanSequence.signedLoopStructureInterval_path X.toKanSequence X.toKanSequence_omega n

end SerrePositivity.KST.Spectra.OmegaSpectrum
