module
public import SerrePositivity.KST.NonConnective.DGKappaSuppliedBFOneStage

/-!
概要：実供給 BF 四角形の同じ cone を、旧 cone の全整数消滅から零と認証する。
方針：指定整数群同型で全群の自明性を移し、元の Sp 零頂点判定へ渡す。
規約：群同型から新旧 BF 対象の Sp 同型を推論しない。I・Z・共終性は保持する。
使われ方：同じ実 fiber を実供給商の native loop へ渡す中央零性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance suppliedBFConeCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：実供給四角形の中間頂点は同じ元 cone の新 BF 模型。
方針：同じ実下辺とその終点を回収する。
規約：旧 kOmegaSpectrum 値との等式ではない。
使われ方：同じ実中央零性を四角形の頂点へ適用する。 -/
theorem dgKappaSuppliedBFSquare_middle :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeCoherentBFSquare R D I) 1 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaNativeBFFiniteOmegaSpectrum R D I
        (dgKappaNativeBFFiniteNativeObject R D I 1)) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target (dgKappaNativeCoherentBFSquare R D I)
  have hb := dgKappaNativeCoherentBFSquare_boundary R D I 0
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgKappaNativeCoherentBFSquare R D I = _ at hb
  rw [hb] at h
  have hv := congrArg (fun t : Sp.{max (u + 1) v} _⦋1⦌ =>
    Sp.{max (u + 1) v}.δ 0 t)
    (SSet.yonedaEquiv.apply_symm_apply
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeCoherentBFArrow R D I 0).hom).edge)
  exact h.symm.trans (hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge _).tgt_eq)

variable (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
  (Z : DGKappaZeroInput R D I)

include hcofinal Z in
/-- 概要：同じ cone の実供給 BF 模型の全整数群は自明。
方針：同じ有限入力の指定整数群同型を逆に使う。
規約：共終性・I・Z に条件付き。実商の零性は主張しない。
使われ方：同じ実 Sp 中央頂点の零性を得る。 -/
theorem dgKappaSuppliedBFCone_subsingleton (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup
      (dgKappaNativeBFFiniteOmegaSpectrum R D I
        (dgKappaNativeBFFiniteNativeObject R D I 1)) j) := by
  let C := dgKappaNativeBFFiniteNativeObject R D I 1
  letI : Subsingleton (OmegaSpectrum.homotopyGroup (kOmegaSpectrum (sInputModel C.obj)) j) := by
    change Subsingleton (OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (dgKappaNativeResolvedCone R D I)) j)
    exact dgKappaNativeResolvedConeK_subsingleton R D I hcofinal Z j
  exact (dgKappaNativeBFIntegerComparisonEquiv R D I C j).symm.injective.subsingleton

include hcofinal Z in
/-- 概要：実供給四角形の同じ中間頂点は Sp の零頂点。
方針：同じ新 BF 模型の全整数群の消滅を元の零頂点判定へ渡す。
規約：共終性・I・Z に条件付きで、旧 BF 頂点の実同型を仮定しない。
使われ方：実供給の fiber 四角形を loop 四角形にする。 -/
theorem dgKappaSuppliedBFSquare_middle_isZero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeCoherentBFSquare R D I) 1 0) := by
  rw [dgKappaSuppliedBFSquare_middle]
  exact spectrum_isZeroVertex_of_homotopyGroup_subsingleton _
    (dgKappaSuppliedBFCone_subsingleton R D I hcofinal Z)

end SerrePositivity.KST.NonConnective
