module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyComparison
public import SerrePositivity.KST.Fibration.SpectrumZeroFromPositiveLevels

/-!
概要：Sp の零頂点の全整数 π 関手の値は一点である。
方針：元の一点スペクトルとの頂点同型を π 関手で送り、既存の一点群の計算を使う。
規約：一点群の計算は既存の K-B 原本を再利用し、複製しない。
使われ方：実 loop 四角形の接続射を全整数次数の自然同型にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumHo

lemma piFunctor_subsingleton_of_isZero (x : hoFunctor.obj Sp.{u})
    (hx : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := Sp.{u}) x.as.as) (j : ℤ) : Subsingleton ((piFunctor j).obj x) := by
  have := Fibration.spectrumPoint_homotopyGroup_subsingleton.{u} j
  let e : x ≅ obj HomotopyLimits.spectrumPoint.{u} :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso hx.2 pointZeroVertex.isTerminal
  let h := (piFunctor j).mapIso e ≪≫ piComparison HomotopyLimits.spectrumPoint j
  exact h.commGroupIsoToMulEquiv.injective.subsingleton

end SerrePositivity.KST.LocalizingInvariants.SpectrumHo
