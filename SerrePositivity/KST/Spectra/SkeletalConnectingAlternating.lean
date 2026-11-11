module

public import SerrePositivity.KST.Spectra.SkeletalPathConnecting
public import SerrePositivity.KST.Spectra.SkeletalPathAlternating

/-!
概要：骨格の通常の制限射の成分接続写像を正規化交代微分で計算する。
方針：実際に path 延長を構成し、その終点と接続写像の成分の一致を交代式へ代入する。
規約：入力は loop 族の実際の辺の逆元。cochain 次数は二以上。
使われ方：Goerss–Jardine VIII §1。骨格の係数微分の正規化交代式への合流。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalPathCoboundary

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：loop 族の逆辺に対する実際の成分接続写像の係数は正規化交代微分。
方針：path 延長の存在と接続写像の値の公式を、延長の終点係数の交代式へ合成する。
規約：延長の選択は結論に残さず、各セルで群の値そのものを計算する。
使われ方：Goerss–Jardine VIII §1。正規化微分と実際の接続写像の符号付き比較。 -/
theorem normalizedDifferential_connecting (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] {n : ℕ}
    (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right)
    (hf : ∀ t : (K.skeleton (n + 3) : SSet.{u}) _⦋n + 1⦌,
      yonedaEquiv.symm t ≫ f = SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)
    (s : K.nonDegenerate (n + 3)) :
    (loopPositiveHomotopyEquiv Y (n + 1)).toAdditive
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
          (AddCommGrpCat.of (Additive
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right (n + 1) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)))
          (n + 2) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f hf) s) =
      (-1 : ℤ) ^ (n + 3) • Additive.ofMul
        (SkeletalCellAttachment.stageFiberComponentEquiv K Y (n + 2)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
            (pointedConnectingZero (UnbasedPointedMapping.pre
              (UnbasedPointedMapping.skeletalInclusion K (n + 2)) Y)
              ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (UnbasedPointedMapping.loopFamilySimplex Y f))⁻¹))) s) := by
  obtain ⟨H, hH⟩ := exists_extension K Y f
  have hc := congrArg (fun z ↦ (-1 : ℤ) ^ (n + 3) • Additive.ofMul
    (SkeletalCellAttachment.stageFiberComponentEquiv K Y (n + 2) z s))
      (componentConnecting_inverse_family K Y f H hH)
  exact (normalizedDifferential_endpointFiber K Y f hf H hH s).trans hc.symm

end
end SerrePositivity.KST.Spectra.SkeletalPathCoboundary
