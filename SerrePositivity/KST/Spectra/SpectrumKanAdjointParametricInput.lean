module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointParametricCoordinates
public import SerrePositivity.KST.Spectra.SignedAdjointParametricInputComparison
public import SerrePositivity.KST.Spectra.PointedBasedPathDifference

/-!
概要：保存済みの Kan 随伴自然性から、元の全 Hom に対する二重 loop 実入力区間を構成する。
方針：元の転置区間を指定三角形付きで逆向きにし、二段の同じ区間を実三角形付きで合成する。
規約：全族自然性や入力 H の存在を仮定しない。使われ方：元の単位構造区間の全族比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

local instance kanAdjointParametricInputInnerKan (Y : OmegaSpectrum.{u}) (n : ℕ) :
    KanComplex (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 1)).space).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance kanAdjointParametricInputParameterKan (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    KanComplex (PointedObject.basedHom (pointedSpace X Y.toKanSequence)
      (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 1)).space)).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の自然性区間・逆向き区間・定数辺を全て保持する、実際の逆三角形。 -/
def kanAdjointParametricInputInverse (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.BasedPathDifference (kanAdjointParametricNaturalityInterval X Y n)
      (PointedMapping.VerticalPath.refl _
        (PointedMapping.transpose (pointedEvaluation X Y.toKanSequence n) ≫
          PointedObject.basedHomMap (pointedSpace X Y.toKanSequence)
            (KanSequence.kanAdjoint Y.toKanSequence n))) :=
  PointedMapping.BasedPathDifference.choose (kanAdjointParametricNaturalityInterval X Y n)
    (PointedMapping.VerticalPath.refl _ _)

/-- 保存済みの実自然性から得た、入力比較に使う同じ逆区間。 -/
def kanAdjointParametricInputInterval (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (PointedObject.basedHom (pointedSpace X Y.toKanSequence)
        (PointedObject.basedHom CirclePower.space.{u} (Y.level (n + 1)).space)))
      (KanSequence.kanAdjoint X.toKanSequence n ≫
        PointedMapping.parametricPost CirclePower.space.{u}
          (pointedEvaluation X Y.toKanSequence (n + 1)))
      (PointedMapping.transpose (pointedEvaluation X Y.toKanSequence n) ≫
        PointedObject.basedHomMap (pointedSpace X Y.toKanSequence)
          (KanSequence.kanAdjoint Y.toKanSequence n)) :=
  (kanAdjointParametricInputInverse X Y n).path

/-- 元の全 Hom の二段の実区間から作った、実入力比較の同じ合成三角形。 -/
def kanAdjointParametricInputComposite (X Y : OmegaSpectrum.{u}) (n : ℕ) :=
  SignedAdjointPaths.parametricInputComparisonComposite
    (KanSequence.kanAdjoint X.toKanSequence n)
    (KanSequence.kanAdjoint X.toKanSequence (n + 1))
    (KanSequence.kanAdjoint Y.toKanSequence n)
    (KanSequence.kanAdjoint Y.toKanSequence (n + 1))
    (PointedMapping.transpose (pointedEvaluation X Y.toKanSequence n))
    (pointedEvaluation X Y.toKanSequence (n + 1))
    (pointedEvaluation X Y.toKanSequence (n + 2))
    (kanAdjointParametricInputInterval X Y n)
    (kanAdjointParametricInputInterval X Y (n + 1))

/-- 元の全 Hom パラメータで無条件に構成した、合成 Kan 随伴の実入力比較区間。 -/
def kanAdjointParametricInputComparison (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (PointedObject.basedHom (pointedSpace X Y.toKanSequence)
        (LoopExchangePaths.doubleLoop (Y.level (n + 2)).space)))
      (SignedAdjointPaths.input (KanSequence.kanAdjoint X.toKanSequence n)
        (KanSequence.kanAdjoint X.toKanSequence (n + 1)) ≫
          LoopExchangePaths.doubleParametricPost
            (pointedEvaluation X Y.toKanSequence (n + 2)))
      (PointedMapping.transpose (pointedEvaluation X Y.toKanSequence n) ≫
        PointedObject.basedHomMap (pointedSpace X Y.toKanSequence)
          (SignedAdjointPaths.input (KanSequence.kanAdjoint Y.toKanSequence n)
            (KanSequence.kanAdjoint Y.toKanSequence (n + 1)))) :=
  (kanAdjointParametricInputComposite X Y n).path

/-- 逆三角形の第一面は、保存済みの元の自然性区間の転置そのもの。 -/
lemma kanAdjointParametricInputInverse_two (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm
      (kanAdjointParametricInputInverse X Y n).triangle.simplex =
        (kanAdjointParametricNaturalityInterval X Y n).path :=
  PointedMapping.BasedPathDifference.triangle_two
    (kanAdjointParametricInputInverse X Y n)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
