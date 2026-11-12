module

public import SerrePositivity.KST.Spectra.SkeletalFiberRepresentatives
public import SerrePositivity.KST.Spectra.SphericalPathBoundary
public import SerrePositivity.KST.Spectra.LoopBoundaryRepresentatives

/-!
概要：loop 値の骨格射を path 空間で一段延長し、終点のセル単体を構成する。
方針：path 空間の全単射への RLP で延長し、終点の定数性と各セル面の一致を厳密に計算する。
規約：向きは既存の loop–path 表示と最後の面の規約を使う。
使われ方：Goerss–Jardine VIII §1。成分微分を正規化交代和で計算する幾何。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalPathCoboundary

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) {n : ℕ}
  (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right)

/-- 概要：loop 値の骨格射の path 表示は、次の骨格へ常に延長できる。
方針：可縮な path 空間の終対象への射の全単射に対する RLP を適用する。
規約：係数 Y の Kan 性だけを要求する。
使われ方：Goerss–Jardine VIII §1。幾何的な coboundary の実際の構成。 -/
theorem exists_extension [KanComplex Y.right] :
    ∃ H : (K.skeleton (n + 4) : SSet.{u}) ⟶ (basedPathSpace Y).right,
      UnbasedPointedMapping.skeletalInclusion K (n + 2) ≫ H =
        f ≫ (PointedMapping.loopToPath Y).right := by
  let i := UnbasedPointedMapping.skeletalInclusion K (n + 2)
  let : Mono i := by
    dsimp only [i, UnbasedPointedMapping.skeletalInclusion]
    infer_instance
  let : HasLiftingProperty i (terminal.from (basedPathSpace Y).right) :=
    basedPathSpace_terminal_rlp Y i inferInstance
  let sq : CommSq (f ≫ (PointedMapping.loopToPath Y).right) i
      (terminal.from (basedPathSpace Y).right)
      (terminal.from (K.skeleton (n + 4) : SSet.{u})) := ⟨Subsingleton.elim _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

variable (H : (K.skeleton (n + 4) : SSet.{u}) ⟶ (basedPathSpace Y).right)
  (hH : UnbasedPointedMapping.skeletalInclusion K (n + 2) ≫ H =
    f ≫ (PointedMapping.loopToPath Y).right)

include hH in
/-- 延長の終点は、元の骨格全体で厳密に定数。 -/
lemma endpoint_lower :
    UnbasedPointedMapping.skeletalInclusion K (n + 2) ≫
      (H ≫ (pathEndpoint Y).right) = SSet.const Y.basepoint := by
  rw [← Category.assoc, hH, Category.assoc, PointedMapping.loopToPath_endpoint, comp_const]

/-- 延長の終点の、指定した新規セルでの境界定数単体。 -/
def endpointSimplex (s : K _⦋n + 3⦌) : Y.right.PtSimplex (n + 3) Y.basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue (H ≫ (pathEndpoint Y).right)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant _ (endpoint_lower K Y f H hH)) s

/-- 指定セルに制限した path の延長。 -/
def cellPath (s : K _⦋n + 3⦌) : (Δ[n + 3] : SSet.{u}) ⟶ (basedPathSpace Y).right :=
  SSet.yonedaEquiv.symm (⟨s, K.mem_skeleton s⟩ : (K.skeleton (n + 4) : SSet.{u}) _⦋n + 3⦌) ≫ H

/-- セルの path の終点は定義したセル単体そのもの。 -/
lemma cellPath_endpoint (s : K _⦋n + 3⦌) :
    cellPath K Y H s ≫ (pathEndpoint Y).right = (endpointSimplex K Y f H hH s).map := rfl

include hH in
/-- 概要：各セル面の path は元の loop の面単体の path 表示と一致する。
方針：顔の Yoneda 射を元の骨格へ戻し、延長の制限式を使う。
規約：セルの面を並べ替えない。
使われ方：Goerss–Jardine VIII §1。球面的 path 境界の交代式への入力。 -/
lemma cellPath_face
    (hf : ∀ t : (K.skeleton (n + 3) : SSet.{u}) _⦋n + 1⦌,
      SSet.yonedaEquiv.symm t ≫ f = SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)
    (s : K _⦋n + 3⦌) (j : Fin (n + 4)) :
    stdSimplex.δ j ≫ cellPath K Y H s =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f hf (K.δ j s)).map ≫
        (PointedMapping.loopToPath Y).right := by
  have he : stdSimplex.δ j ≫ SSet.yonedaEquiv.symm
        (⟨s, K.mem_skeleton s⟩ : (K.skeleton (n + 4) : SSet.{u}) _⦋n + 3⦌) =
      SSet.yonedaEquiv.symm
          (⟨K.δ j s, K.mem_skeleton _⟩ : (K.skeleton (n + 3) : SSet.{u}) _⦋n + 2⦌) ≫
        UnbasedPointedMapping.skeletalInclusion K (n + 2) := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, yonedaEquiv_symm_comp]
    rfl
  change stdSimplex.δ j ≫ (SSet.yonedaEquiv.symm _ ≫ H) = _
  rw [← Category.assoc, he, Category.assoc, hH]
  rfl

/-- 延長の終点を、次の骨格の実際の fiber の頂点として表す。 -/
def endpointFiberVertex : (UnbasedPointedMapping.stageFiber K Y (n + 2)).right _⦋0⦌ :=
  SkeletalCellAttachment.skeletalFiberVertex K Y (n + 2) (H ≫ (pathEndpoint Y).right)
    (endpoint_lower K Y f H hH)

/-- 延長の終点の実際の fiber 成分の係数は、同じ終点のセル単体の類。 -/
lemma endpointFiberVertex_coefficient [KanComplex Y.right] (s : K.nonDegenerate (n + 3)) :
    SkeletalCellAttachment.stageFiberComponentEquiv K Y (n + 2)
        (π₀.mk (endpointFiberVertex K Y f H hH)) s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (endpointSimplex K Y f H hH s.val) := by
  have hc := congrFun (SkeletalCellAttachment.skeletalFiberVertex_cochain K Y (n + 1)
    (H ≫ (pathEndpoint Y).right) (endpoint_lower K Y f H hH)) s
  change Additive.ofMul (SkeletalCellAttachment.stageFiberComponentEquiv K Y (n + 2)
    (π₀.mk (endpointFiberVertex K Y f H hH)) s) =
      Additive.ofMul (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (endpointSimplex K Y f H hH s.val)) at hc
  exact congrArg Additive.toMul hc

end
end SerrePositivity.KST.Spectra.SkeletalPathCoboundary
