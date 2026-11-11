module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceRoof
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorQuasiIsoFullyFaithful
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CellDGResolutionNerve

/-!
概要：元対角始域の cell 分解と同じ thick 平坦核の native 同値を構成する。
方針：元対角の Milnor 判定と同じ平坦核の本質像を使い、全写像空間と本質的全射性を示す。
規約：元始域は同じ増大屋根の終端として保つ。
使われ方：d④ の核比較の ν 同値と元対角の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal_isExactFunctor R d
local notation "A" => DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.source d))
local notation "B" => DGOdotGluing R d
local notation "δ" => DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d)
local notation "P" => dgQuotientImage R (δ)
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R (B) (P)
local notation "I" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickKernelInclusion R (B) (P)

/-- 概要：同じ厳密核比較を含めると元対角と増大の合成を全単体で回収する。
方針：元の dg 可換式を同じ nerve に写す。規約：全関手の等号。
使われ方：核比較の本質的全射性。 -/
lemma dgOdotMilnorSourceKernelNerve_augmentation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorSourceKernelDGMap R d) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (A)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, dgOdotMilnorSourceKernelDGMap_augmentation, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]

/-- 概要：Milnor 条件から同じ核比較の native 充満忠実性。
方針：証明済みの全 Hom 準同型性を D の写像空間判定へ渡す。
規約：h 圏の充満忠実性だけに弱めない。使われ方：実 native 同値の第一欄。 -/
lemma dgOdotMilnorSourceKernelNerve_fullyFaithful (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorSourceKernelDGMap R d)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_quasiIso _
    (dgOdotMilnorSourceKernelDGMap_homQuasiIso R d h)

/-- 概要：同じ核比較の全ての native 対象は像の対象と同型。
方針：平坦核の本質像と元対角の像を照合し、同じ増大同値で始域を戻す。
規約：対象の等号や逆 dg 関手を要求しない。使われ方：実 native 同値の第二欄。 -/
lemma dgOdotMilnorSourceKernelNerve_essentiallySurjective (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorSourceKernelDGMap R d)) := by
  intro y
  let b := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)).app (Opposite.op ⦋0⦌) y
  have hb : b ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal R d) := by
    rw [← dgOdotMilnorFlatKernel_image_eq_diagonal R d h]
    exact ⟨y, ⟨Iso.refl _⟩⟩
  obtain ⟨a, ⟨v⟩⟩ := hb
  let E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (A)
  let x := E.inv.app (Opposite.op ⦋0⦌) a
  have vi := ((E.invHomIso.app a).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ))).trans v
  have hx := congrArg (fun f => f.app (Opposite.op ⦋0⦌) x)
    (dgOdotMilnorSourceKernelNerve_augmentation R d)
  have vi' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorSourceKernelDGMap R d)).app (Opposite.op ⦋0⦌) x)) b := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (δ)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (A))).app
        (Opposite.op ⦋0⦌) x)) b at vi
    exact hx.symm ▸ vi
  exact ⟨x, ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickKernelInclusion_isFullyFaithful R (B) (P)).preimageVertexIso
    vi'⟩⟩

/-- 概要：Milnor 条件から同じ厳密核比較の native 同値。
方針：実写像空間の充満忠実性と本質的全射性を束ねる。
規約：同値の順方向は元の厳密比較そのもの。使われ方：元始域の指定 ν 比較。 -/
theorem dgOdotMilnorSourceKernelNerve_isQCatEquivalence (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorSourceKernelDGMap R d)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (dgOdotMilnorSourceKernelNerve_fullyFaithful R d h)
    (dgOdotMilnorSourceKernelNerve_essentiallySurjective R d h)

end SerrePositivity.KST.SConstruction
