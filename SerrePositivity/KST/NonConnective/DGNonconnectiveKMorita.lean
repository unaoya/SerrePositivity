module
public import SerrePositivity.KST.NonConnective.DGNonconnectiveK
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFMorita
public import SerrePositivity.KST.NonConnective.DGSuspensionUnconditionalIterationMorita

/-!
概要：各実懸垂段の元の Morita 射と可換な実逐次比較を、同じ非連結 K へ送る。
方針：K-4 の元の BF 射の π 同型を native loop 座標で戻し、実余極限比較へ渡す。
規約：実逐次比較・各懸垂段の dg 射・座標可換性は明示入力。c4 の供給は推論しない。
使われ方：K-7 e の Morita 保存の利用側。初期射だけからの全段保存は別工程。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance ncKMoritaSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A B : PerfDGInput.{u, max (u + 1) v} R)
  (η : dgNonconnectiveKDiagram R κ hκ A ⟶ dgNonconnectiveKDiagram R κ hκ B)

/-- 同じ実逐次比較が与える、元の二つの非連結 K 間の実 BF 射。 -/
def dgNonconnectiveKMap : dgNonconnectiveK R κ hκ A ⟶ dgNonconnectiveK R κ hκ B :=
  sequentialCandidateMap η

variable (f : ∀ n : ℕ, dgSuspensionUnconditionalIteration R κ hκ A n ⟶
    dgSuspensionUnconditionalIteration R κ hκ B n)
  (hf : ∀ n : ℕ, (quasiEquivalencePerfectExtension R
    (dgSuspensionUnconditionalIteration R κ hκ A n)
    (dgSuspensionUnconditionalIteration R κ hκ B n) (f n).down).IsEquivalence)
  (h : ∀ (n : ℕ) (j : ℤ)
    (x : OmegaSpectrum.homotopyGroup (dgNonconnectiveKStage R κ hκ A n) j),
    dgNonconnectiveKStage_piEquiv R κ hκ B n j (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x) =
      OmegaSpectrum.homotopyMap (dgKInputSpectrumMap R (f n)) (j + n)
        (dgNonconnectiveKStage_piEquiv R κ hκ A n j x))
include hf h

/-- 概要：同じ段別 Morita 比較から、非連結 K 比較の全整数 π 同型。
方針：元の実 K 射を使う K-4 の Morita 判定を、指定の同じ座標で消去する。
規約：η・f・hf・h に条件付き。初期 Morita 射からの c4 の存在は結論しない。
使われ方：e の全段保存と全入力作用が供給された後の、同じ実候補上の不変性。 -/
theorem dgNonconnectiveKMap_piIsomorphism_of_stagewise_morita :
    OmegaSpectrum.PiIsomorphism (dgNonconnectiveKMap R κ hκ A B η) := by
  apply sequentialCandidateMap_piIsomorphism η
  intro a j
  let n := a.down
  let := hf n
  have hc := presentedPerfectDGBFMap_morita_piIsomorphism R (f n) (j + n)
  let eA := dgNonconnectiveKStage_piEquiv R κ hκ A n j
  let eB := dgNonconnectiveKStage_piEquiv R κ hκ B n j
  have he : eB ∘ OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j =
      OmegaSpectrum.homotopyMap (dgKInputSpectrumMap R (f n)) (j + n) ∘ eA :=
    funext (h n j)
  have ht : Function.Bijective (eB ∘ OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j) := by
    rw [he]
    exact hc.comp eA.bijective
  exact ⟨fun _ _ heq => ht.injective (congrArg eB heq), fun y => by
    obtain ⟨x, hx⟩ := ht.surjective (eB y)
    exact ⟨x, eB.injective hx⟩⟩

/-- 同じ実非連結 K 比較の Sp 辺は可逆。 -/
theorem dgNonconnectiveKMap_isInvertible_of_stagewise_morita :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgNonconnectiveKMap R κ hκ A B η)) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (dgNonconnectiveKMap_piIsomorphism_of_stagewise_morita R κ hκ A B η f hf h)

omit hf h in
/-- 初期 Morita 射から全段保存を放電し、元の実逐次比較の π 同型を得る。
実逐次比較と元の loop 座標の可換性は到着する c4 の作用から供給する。 -/
theorem dgNonconnectiveKMap_piIsomorphism_of_initial_morita
    (f₀ : A ⟶ B) [(quasiEquivalencePerfectExtension R A B f₀.down).IsEquivalence]
    (hη : ∀ (n : ℕ) (j : ℤ)
      (x : OmegaSpectrum.homotopyGroup (dgNonconnectiveKStage R κ hκ A n) j),
      dgNonconnectiveKStage_piEquiv R κ hκ B n j
          (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x) =
        OmegaSpectrum.homotopyMap (dgKInputSpectrumMap R
          (dgSuspensionUnconditionalIterationMap R κ hκ f₀ n)) (j + n)
          (dgNonconnectiveKStage_piEquiv R κ hκ A n j x)) :
    OmegaSpectrum.PiIsomorphism (dgNonconnectiveKMap R κ hκ A B η) :=
  dgNonconnectiveKMap_piIsomorphism_of_stagewise_morita R κ hκ A B η
    (dgSuspensionUnconditionalIterationMap R κ hκ f₀)
    (dgSuspensionUnconditionalIterationMap_perfect_isEquivalence R κ hκ f₀) hη

omit hf h in
/-- 同じ実逐次比較の辺は、初期 Morita 射と実 loop 座標可換性から可逆。 -/
theorem dgNonconnectiveKMap_isInvertible_of_initial_morita
    (f₀ : A ⟶ B) [(quasiEquivalencePerfectExtension R A B f₀.down).IsEquivalence]
    (hη : ∀ (n : ℕ) (j : ℤ)
      (x : OmegaSpectrum.homotopyGroup (dgNonconnectiveKStage R κ hκ A n) j),
      dgNonconnectiveKStage_piEquiv R κ hκ B n j
          (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x) =
        OmegaSpectrum.homotopyMap (dgKInputSpectrumMap R
          (dgSuspensionUnconditionalIterationMap R κ hκ f₀ n)) (j + n)
          (dgNonconnectiveKStage_piEquiv R κ hκ A n j x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgNonconnectiveKMap R κ hκ A B η)) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (dgNonconnectiveKMap_piIsomorphism_of_initial_morita R κ hκ A B η f₀ hη)

end SerrePositivity.KST.NonConnective
