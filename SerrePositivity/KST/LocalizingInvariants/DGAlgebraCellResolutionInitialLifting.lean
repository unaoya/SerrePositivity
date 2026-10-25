module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolutionArbitraryLift
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
概要：native cell 分解への始対象射は、全射擬同型に対して左持ち上げ性を持つ。
方針：元の cell 任意射の実 lift を使い、始対象からの二射の一致で左辺を回収する。
規約：モデル構造や cofibrancy の instance を入力しない。
使われ方：構成済みの実代数モデルの cofibration 判定へ native cell 分解を代入する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

lemma cellResolution_initial_hasLiftingProperty {I X Y : Mon (Complex R)}
    (hI : IsInitial I) (p : X ⟶ Y) (hs : (∀ n : ℤ, Function.Surjective (p.hom.f n)))
    (hq : QuasiIso p.hom) : HasLiftingProperty (hI.to (cellResolution R A)) p where
  sq_hasLift := fun {a b} _ => by
    obtain ⟨c, hc⟩ := exists_cellResolutionArbitraryLift R p hs hq b
    exact ⟨c, hI.hom_ext _ _, hc⟩

lemma cellResolution_initial_llp {I : Mon (Complex R)} (hI : IsInitial I) :
    MorphismProperty.llp
      (fun {X Y : Mon (Complex R)} (p : X ⟶ Y) =>
        (∀ n : ℤ, Function.Surjective (p.hom.f n)) ∧ QuasiIso p.hom)
        (hI.to (cellResolution R A)) := by
  intro X Y p hp
  exact cellResolution_initial_hasLiftingProperty R A hI p hp.1 hp.2

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
