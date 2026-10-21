module

public import SerrePositivity.KST.Spectra.CofibrantSequenceLifting
public import SerrePositivity.KST.Spectra.FiberOmegaSpectrum

/-!
概要：cofibrant な BF 源からの列の持ち上げを実 BF 射と比較式に束ねる。
方針：既存の単射に対する帰納充填を、変数である源・標的に対して一度適用する。
規約：各段の比較式をデータに保持。使われ方：fiber の置換比較と整数 π の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants

structure CofibrantSpectrumLift {X W : OmegaSpectrum.{u}} {Z : KanSequence.{u}}
    (q : KanSequence.Hom W.toKanSequence Z) (f : KanSequence.Hom X.toKanSequence Z) where
  map : X ⟶ W
  fac : ∀ n, map.app n ≫ q.app n = f.app n

def cofibrantSpectrumLift {X W : OmegaSpectrum.{u}} {Z : KanSequence.{u}}
    (q : KanSequence.Hom W.toKanSequence Z)
    (hq : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (q.app n).right)
    (f : KanSequence.Hom X.toKanSequence Z) : CofibrantSpectrumLift q f := by
  let l := KanSequence.liftHom X.sigma_mono q hq f
  exact ⟨⟨l.app, l.comm⟩, KanSequence.liftHom_fac X.sigma_mono q hq f⟩

end SerrePositivity.KST.LocalizingInvariants
