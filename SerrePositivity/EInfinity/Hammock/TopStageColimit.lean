module

public import SerrePositivity.EInfinity.Hammock.WordTopFinal
public import SerrePositivity.EInfinity.Hammock.LengthStage

/-!
# 最大長の交互方向語だけによる元の段階の余極限

概要：前段階の全語と最大長の交互方向語の図式から、元の段階の余極限を回収する。
方針：元の全部分圏の包含の Final 性と標準の colimit.pre を使う。
規約：proper 性は不要。元の固定語の標準射への一致も保持する。
使われ方：長さ段階の pushout の普遍性。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits

variable (F : Word ⥤ SSet.{w}) (n : ℕ)

def topStageDiagram : Word.TopStage n ⥤ SSet.{w} :=
  Word.topStageInclusion n ⋙ (Word.lengthInclusion n ⋙ F)

/-- 元の包含が定める、交互方向の最大語の図式と元の段階の余極限の同型。 -/
def topStageColimitIso : colimit (topStageDiagram F n) ≅ lengthStage F n := by
  let := Word.topStageFinal n
  exact Functor.Final.colimitIso (Word.topStageInclusion n) (Word.lengthInclusion n ⋙ F)

lemma topStageColimitIso_fac (a : Word.TopStage n) :
    colimit.ι (topStageDiagram F n) a ≫ (topStageColimitIso F n).hom =
      lengthStageInclusion F n a.obj.obj a.obj.property := by
  let := Word.topStageFinal n
  exact Functor.Final.ι_colimitIso_hom (Word.topStageInclusion n)
    (Word.lengthInclusion n ⋙ F) a

end SerrePositivity.EInfinity.Hammock
