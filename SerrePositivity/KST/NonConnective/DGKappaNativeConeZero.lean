module
public import SerrePositivity.KST.NonConnective.DGKappaNativeConeResolution
public import SerrePositivity.KST.Fibration.SpectrumZeroFromPositiveLevels

/-!
概要：同じ実平坦 cone の完備化前の K を実 Sp 零頂点として認証する。
方針：構成済みの全整数群の消滅を K-B の元の零頂点判定へ渡す。
規約：同じ I・Z と共終性命題に条件付き。実商の零性は主張しない。
使われ方：K-7 c5 の完備化前の実 fibration の中央項。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance nativeConeZeroSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))

include hcofinal in
/-- 概要：共終性と同じ零所属に条件付きで、同じ実平坦源の native K は実 Sp 零頂点。
方針：同じ全整数群の消滅から元の一点スペクトルとの実同型を使う。
規約：元の cell 増大・cone・K 値を保持し、存在仮定や Sp 引き戻し性を追加しない。
使われ方：完備化前の実 fiber を同じ実商の loop と比較する中央零性。 -/
theorem dgKappaNativeResolvedConeK_isZeroVertex (Z : DGKappaZeroInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum (dgKappaNativeResolvedCone R D I))) :=
  Fibration.spectrum_isZeroVertex_of_homotopyGroup_subsingleton _
    (dgKappaNativeResolvedConeK_subsingleton R D I hcofinal Z)

end SerrePositivity.KST.NonConnective
