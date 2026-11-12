module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionNuChoiceCoherence
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionKChoiceComparison
public import SerrePositivity.KST.NonConnective.DGKappaFixedKComparisonPi
public import SerrePositivity.KST.SConstruction.StableKFunctorIsoInvariance

/-!
概要：元の固定 K 選択射の全整数 π 作用が恒等・三選択合成を保つことを証明する。
方針：固定 ν の比較を SOA K へ送り、中間の元の BF 順逆比較を π 上で縮約する。
規約：BF 射自体の厳密関手則や全入力作用は主張しない。固定 K を変更しない。
使われ方：K-7 d4 の模型選択比較を元の実整数 K 群の整合した比較へ接続する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I J K : DGKappaConeInput R A κ)
  (P : DGKappaPerfectInput R A I) (Q : DGKappaPerfectInput R A J)
  (T : DGKappaPerfectInput R A K) (j : ℤ)

/-- 自己選択の元の固定 BF K 射は、同じ全整数 π 上で恒等。 -/
theorem dgKappaSuspensionKChoiceMap_pi_self :
    OmegaSpectrum.homotopyMap (dgKappaSuspensionKChoiceMap R A I I P P) j =
      MonoidHom.id _ := by
  let f := (dgKappaSuspensionStableChoiceEquivalence R A I I P P).hom
  have he := kHomotopyMap_eq_of_exact_functorIso f (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (dgKappaSuspensionNuChoiceEquivalence R A I I P P).isQCatEquivalence)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_id _) (dgKappaSuspensionNuChoice_selfIso R A I P) j
  have hk : kHomotopyMap f j = MonoidHom.id _ := he.trans (kHomotopyMap_id _ j)
  simp only [dgKappaSuspensionKChoiceMap, dgKappaFixedKChoiceMap,
    dgKappaFixedKChoiceSOAMap, OmegaSpectrum.homotopyMap_comp]
  change (OmegaSpectrum.homotopyMap
    (presentedPerfectDGBFSOASpectrumComparison R (dgKappaSuspensionKInput R A I)) j).comp
      ((kHomotopyMap f j).comp (OmegaSpectrum.homotopyMap
        (presentedPerfectDGBFSOAInverseComparison R (dgKappaSuspensionKInput R A I)) j)) = _
  rw [hk, MonoidHom.id_comp]
  exact dgKappaFixedKComparisonPi_right R (dgKappaSuspensionKInput R A I) j

/-- 三選択の元の実 BF 比較の π 作用は、同じ直接比較の π 作用と一致する。 -/
theorem dgKappaSuspensionKChoiceMap_pi_comp :
    OmegaSpectrum.homotopyMap (dgKappaSuspensionKChoiceMap R A I K P T) j =
      (OmegaSpectrum.homotopyMap (dgKappaSuspensionKChoiceMap R A J K Q T) j).comp
        (OmegaSpectrum.homotopyMap (dgKappaSuspensionKChoiceMap R A I J P Q) j) := by
  let f := (dgKappaSuspensionStableChoiceEquivalence R A I J P Q).hom
  let g := (dgKappaSuspensionStableChoiceEquivalence R A J K Q T).hom
  let h := (dgKappaSuspensionStableChoiceEquivalence R A I K P T).hom
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.val := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
    (dgKappaSuspensionNuChoiceEquivalence R A I J P Q).isQCatEquivalence
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor g.val := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
    (dgKappaSuspensionNuChoiceEquivalence R A J K Q T).isQCatEquivalence
  have he := kHomotopyMap_eq_of_exact_functorIso (f ≫ g) h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp f.val g.val)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (dgKappaSuspensionNuChoiceEquivalence R A I K P T).isQCatEquivalence)
    (dgKappaSuspensionNuChoice_compIso R A I J K P Q T) j
  have hk : kHomotopyMap h j = (kHomotopyMap g j).comp (kHomotopyMap f j) :=
    he.symm.trans (kHomotopyMap_comp f g j)
  apply MonoidHom.ext
  intro x
  simp only [dgKappaSuspensionKChoiceMap, dgKappaFixedKChoiceMap,
    dgKappaFixedKChoiceSOAMap, OmegaSpectrum.homotopyMap_comp, MonoidHom.comp_apply]
  change OmegaSpectrum.homotopyMap
    (presentedPerfectDGBFSOASpectrumComparison R (dgKappaSuspensionKInput R A K)) j
      (kHomotopyMap h j (OmegaSpectrum.homotopyMap
        (presentedPerfectDGBFSOAInverseComparison R (dgKappaSuspensionKInput R A I)) j x)) =
    OmegaSpectrum.homotopyMap
      (presentedPerfectDGBFSOASpectrumComparison R (dgKappaSuspensionKInput R A K)) j
      (kHomotopyMap g j (OmegaSpectrum.homotopyMap
        (presentedPerfectDGBFSOAInverseComparison R (dgKappaSuspensionKInput R A J)) j
        (OmegaSpectrum.homotopyMap
          (presentedPerfectDGBFSOASpectrumComparison R (dgKappaSuspensionKInput R A J)) j
          (kHomotopyMap f j (OmegaSpectrum.homotopyMap
            (presentedPerfectDGBFSOAInverseComparison R (dgKappaSuspensionKInput R A I)) j x)))))
  rw [hk, MonoidHom.comp_apply]
  have hc := congrArg (fun t => t (kHomotopyMap f j (OmegaSpectrum.homotopyMap
    (presentedPerfectDGBFSOAInverseComparison R (dgKappaSuspensionKInput R A I)) j x)))
      (dgKappaFixedKComparisonPi_left R (dgKappaSuspensionKInput R A J) j)
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at hc
  rw [hc]

end SerrePositivity.KST.NonConnective
