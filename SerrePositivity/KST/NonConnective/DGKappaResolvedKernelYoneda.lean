module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedKernelRepresentability
public import SerrePositivity.KST.NonConnective.DGKappaResolvedKernelComplete
public import SerrePositivity.InfinityCategories.Derived.DGPerfectYonedaIdempotentCompletion
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompleteImageRetracts

/-!
概要：同じ実小核の元の dg Yoneda は、その実 Perf への native 同値となる。
方針：同じ核の前三角性と冪等完備性を D 正本の Yoneda 完備化へ代入する。
規約：同じ明示 I に条件付き。I の実例や異なる入力間の自然性は主張しない。
使われ方：K-7 c5 の実小核とその Perf の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
local notation "C" => dgKappaResolvedKernelKInput R D I

/-- 概要：同じ実小核の対象ラベルの上げ下げを native nerve の実同型として保持する。
方針：D 正本の元の上げ下げ dg 関手と合成等式をそのまま写す。
規約：対象宇宙が既に共通宇宙にある同じ実核に限る。
使われ方：元の核の冪等完備性を同じ Yoneda の始域へ移す。 -/
def dgKappaResolvedKernelLiftIso :
    dgNerve R (C) ≅ dgNerve R (DGUniverseLift.{max (u+1) v, max (u+1) v} (C)) where
  hom := dgNerve.map (dgUniverseLiftUp R (C))
  inv := dgNerve.map (dgUniverseLiftDown R (C))
  hom_inv_id := by
    rw [← dgNerve.map_comp, dgUniverseLiftUp_comp_down, dgNerve.map_id]
  inv_hom_id := by
    rw [← dgNerve.map_comp, dgUniverseLiftDown_comp_up, dgNerve.map_id]

/-- 概要：同じ実核の dg Yoneda 完備化は元の native 関手そのものの同値である。
方針：実核の前三角性から完備化を得て、同じ実核の冪等完備性で retract を像へ戻す。
規約：同じ I に条件付き。P は D-8 e の実供給を使う。
使われ方：実小核からその Perf への比較を、追加の存在入力なしで使う。 -/
theorem dgKappaResolvedKernelYoneda_isQCatEquivalence :
    IsQCatEquivalence (dgPerfectYonedaInfinity R (C)) := by
  let := dgKappaResolvedKernel_isDGPretriangulated R D I
  have hY := dgPerfectYonedaInfinity_isIdempotentCompletion R (C)
  have hC := (dgKappaResolvedKernelNerve_isIdempotentComplete R D I
    (dgKappaPerfectInput R D I)).of_equivalence
      (qCatEquivalenceOfIso (dgKappaResolvedKernelLiftIso R D I))
  apply isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _ hY.2.1
  intro z
  obtain ⟨c, ⟨r⟩⟩ := hY.2.2 z
  obtain ⟨c', ⟨e⟩⟩ := hC.retract_iso_in_image _ hY.2.1 c z r
  exact ⟨c', ⟨e.symm⟩⟩

/-- 概要：同じ実核から出る元の dg Yoneda を、対象ラベルの移送後も厳密に回収する。
方針：D 正本の上げ下げの等式を、元の全 Hom 写像の合成へ代入する。
規約：同じ I の同じ実核と同じ Yoneda 関手を使う。
使われ方：共通宇宙の完備化比較を元の入力の全単体へ戻す。 -/
theorem dgKappaResolvedKernelYoneda_lift :
    (dgKappaResolvedKernelLiftIso R D I).hom ≫ dgPerfectYonedaInfinity R (C) =
      dgNerve.map (dgPerfectYoneda R (C)) := by
  change dgNerve.map (dgUniverseLiftUp R (C)) ≫
    dgNerve.map (dgPerfectYonedaCommonFunctor R (C)) = _
  rw [← dgNerve.map_comp]
  congr 1

/-- 概要：元の実核からその Perf への元の dg Yoneda 自身が native 同値である。
方針：同じ対象ラベルの実同型と構成済みの完備化同値を合成する。
規約：I に条件付きであり、独立の P は要求しない。
使われ方：K-7 c5 の元の実核と Perf の照合。 -/
theorem dgKappaResolvedKernelYonedaOriginal_isQCatEquivalence :
    IsQCatEquivalence (dgNerve.map (dgPerfectYoneda R (C))) := by
  rw [← dgKappaResolvedKernelYoneda_lift R D I]
  exact (qCatEquivalenceOfIso (dgKappaResolvedKernelLiftIso R D I)).isQCatEquivalence.comp
    (dgKappaResolvedKernelYoneda_isQCatEquivalence R D I)

end SerrePositivity.KST.NonConnective
