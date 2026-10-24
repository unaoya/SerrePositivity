module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionInputLaws

/-!
概要：同じ明示懸垂入力射の恒等・合成則を、固定 dg K の元の実 Sp 射へ送る。
方針：厳密入力射の等式と、K-S• 正本の同じ BF 射の厳密関手則を使う。
規約：群作用やホモトピー圏の等式で代用せず、元の実 spectrum 射を保持する。
使われ方：同じ増大可換データに関する反復懸垂の固定 K 屋根の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 元の恒等懸垂入力射の固定 K 像は、元の同じ spectrum の厳密恒等射。 -/
theorem dgKappaSuspensionSpectrumMap_id :
    dgKInputSpectrumMap R
        (dgKappaSuspensionInputMap R D D I I (DGKappaSuspensionMapData.id R D I)) =
      𝟙 (dgKInputSpectrum R (dgKappaSuspensionKInput R D I)) := by
  rw [dgKappaSuspensionInputMap_id]
  exact presentedPerfectDGBFMap_id R _

/-- 同じ明示データの懸垂射の合成は、固定 K の元の実 spectrum 射の厳密合成に移る。 -/
theorem dgKappaSuspensionSpectrumMap_comp
    {E F : Type v} [DGCategory R E] [DGCategory R F] [Small.{u} E] [Small.{u} F]
    {J : DGKappaConeInput R E κ} {K : DGKappaConeInput R F κ}
    (M : DGKappaSuspensionMapData R D E I J) (N : DGKappaSuspensionMapData R E F J K) :
    dgKInputSpectrumMap R
        (dgKappaSuspensionInputMap R D F I K (DGKappaSuspensionMapData.comp R D E I J M N)) =
      dgKInputSpectrumMap R (dgKappaSuspensionInputMap R D E I J M) ≫
        dgKInputSpectrumMap R (dgKappaSuspensionInputMap R E F J K N) := by
  rw [dgKappaSuspensionInputMap_comp]
  exact presentedPerfectDGBFMap_comp R _ _

end SerrePositivity.KST.NonConnective
