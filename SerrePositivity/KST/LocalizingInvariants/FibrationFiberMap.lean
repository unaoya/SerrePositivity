module

public import SerrePositivity.KST.LocalizingInvariants.FibrationFiberSequenceMap
public import SerrePositivity.KST.LocalizingInvariants.CofibrantSpectrumLift

/-!
概要：厳密な fibration 正方形から元の BF fiber の間の実射を構成する。
方針：置換前の fiber 列の射を cofibrant な源から単射置換の比較射へ持ち上げる。
規約：選択した持ち上げの各段の比較式を保持。使われ方：接続射の整数次数の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FibrationFiberComparison
variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  [hp : ∀ n, Fibration (p.app n).right] [hq : ∀ n, Fibration (q.app n).right]
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def projection : KanSequence.Hom (fiber p hp).toKanSequence ((sequenceHom p).fiber hp) :=
  KanSequence.replacementProjection ((sequenceHom p).fiber hp)

def liftData : CofibrantSpectrumLift (projection q)
    ((projection p).comp (sequenceMap p q a b h)) :=
  cofibrantSpectrumLift (projection q)
    (fun n => (KanSequence.replacementStage ((sequenceHom q).fiber hq) n).projection_rlp)
    ((projection p).comp (sequenceMap p q a b h))

def map : fiber p hp ⟶ fiber q hq := (liftData p q a b h).map

lemma map_level (n : ℕ) : (map p q a b h).app n ≫ fiberLevelProjection q hq n =
    fiberLevelProjection p hp n ≫ level p q a b h n :=
  (liftData p q a b h).fac n

lemma map_inclusion : map p q a b h ≫ fiberInclusion q hq = fiberInclusion p hp ≫ a := by
  apply OmegaSpectrum.Hom.ext
  intro n
  change (map p q a b h).app n ≫ (fiberLevelProjection q hq n ≫ pointedFiberι (q.app n)) =
    (fiberLevelProjection p hp n ≫ pointedFiberι (p.app n)) ≫ a.app n
  rw [← Category.assoc, map_level, Category.assoc, level_ι, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.FibrationFiberComparison
