module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumBinaryFunctor
public import SerrePositivity.KST.Spectra.Limits.SpectrumHomFibrations

/-!
概要：Kan な第二因子を持つ単体的積の第一射影と、元の BF 積の段ごとの第一射影の fibration 性。
方針：第一成分を底から固定し、第二成分を Kan ホーン充填で持ち上げる。
規約：モデル圏の instance は入力しない。使われ方：積射影の実 ∞ pullback。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.Binary

lemma projection_fibration (X Y : SSet.{u}) [KanComplex Y] :
    Fibration (CartesianMonoidalCategory.fst X Y) := by
  apply (fibration_iff _).2
  intro T U j hj
  have hy : J.rlp (terminal.from Y) := (fibration_iff _).1 inferInstance
  have : HasLiftingProperty j (terminal.from Y) := hy j hj
  constructor
  intro a b sq
  let sy : CommSq (a ≫ CartesianMonoidalCategory.snd X Y) j
      (terminal.from Y) (terminal.from U) := ⟨terminalIsTerminal.hom_ext _ _⟩
  refine ⟨⟨{
    l := CartesianMonoidalCategory.lift b sy.lift
    fac_left := ?_
    fac_right := CartesianMonoidalCategory.lift_fst _ _ }⟩⟩
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, CartesianMonoidalCategory.lift_fst]
    exact sq.w.symm
  · rw [Category.assoc, CartesianMonoidalCategory.lift_snd]
    exact sy.fac_left

instance fst_level_fibration (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    Fibration ((Binary.fst X Y).app n).right := by
  change Fibration (CartesianMonoidalCategory.fst (X.level n).space.right (Y.level n).space.right)
  exact projection_fibration _ _

end SerrePositivity.KST.LocalizingInvariants.Binary
