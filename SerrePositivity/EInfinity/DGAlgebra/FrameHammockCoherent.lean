module

public import SerrePositivity.EInfinity.DGAlgebra.FrameLocalizationInput
public import SerrePositivity.EInfinity.FrameHom.RightFrameHammockCoherent

/-!
概要：実 dg right frame と元の hammock の全標的 coherent 比較。
方針：同じ自由 I/J の小対象論法による全分解データを一般比較へ代入する。
規約：追加のモデル・関手的分解仮定なし、cofibrant 源だけを条件にする。
使われ方：Sp の全擬同型 ∞ 局所化の写像空間比較への接続。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.DGAlgebra
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R]

/-- 概要：実 dg right Hom と実 hammock Hom は全標的で coherent に自然同型。
方針：実自由 I/J による分解と同じ実 frame を全六辺の比較へ代入する。
規約：追加入力は元の源の cofibrancy のみ。
使われ方：Sp が全標的の比較を coherent に合成する入口。 -/
def rightFrameHammockCoherentComparison (X : Mon (Complex R)) :
    letI _modelInst := modelCategory R
    IsCofibrant X →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
        (FrameHom.rightFrameHammockCoherentDiagram ((sourceFrameFamily R).atObject X)
          (rightFrameFamily R) 0)
        (FrameHom.rightFrameHammockCoherentDiagram ((sourceFrameFamily R).atObject X)
          (rightFrameFamily R) 6) := by
  letI _modelInst := modelCategory R
  intro hX
  letI _sourceCofibrant := hX
  exact FrameHom.rightFrameHammockCoherentComparison ((sourceFrameFamily R).atObject X)
    (rightFrameFamily R) (cofibrantFactorization R)

/-- 概要：同じ実 dg 比較は任意の全標的図式の前合成でも保持される。
方針：同じ一つの全関手同型を指定したパラメータで前合成する。
規約：全図式の自然性。使われ方：Sp の実 frame 比較の全図式への適用。 -/
def rightFrameHammockCoherentComparison_precomp (X : Mon (Complex R)) :
    letI _modelInst := modelCategory R
    IsCofibrant X →
      ∀ {K : SSet.{u + 2}}
        (f : K ⟶ SSet.uliftFunctor.{u + 2, u + 1}.obj
          (nerve (AsSmall.{u + 1} (Mon (Complex R))))),
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
          (f ≫ FrameHom.rightFrameHammockCoherentDiagram ((sourceFrameFamily R).atObject X)
            (rightFrameFamily R) 0)
          (f ≫ FrameHom.rightFrameHammockCoherentDiagram ((sourceFrameFamily R).atObject X)
            (rightFrameFamily R) 6) := by
  letI _modelInst := modelCategory R
  intro hX K f
  exact (rightFrameHammockCoherentComparison R X hX).precomp f

end SerrePositivity.EInfinity.DGAlgebra
