module

public import SerrePositivity.KST.Spectra.FiberOmegaSpectrum
public import SerrePositivity.KST.Spectra.PointedFiberComparison

/-!
概要：段ごとの fibration の厳密な可換正方形から、置換前の fiber 列の射を構成する。
方針：各段の点つき fiber 比較を取り、包含の単射性で構造射の可換性を検証する。
規約：BF の置換前後を区別。使われ方：整数次数の接続射の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FibrationFiberComparison
variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  [hp : ∀ n, Fibration (p.app n).right] [hq : ∀ n, Fibration (q.app n).right]
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def level (n : ℕ) : pointedFiber (p.app n) ⟶ pointedFiber (q.app n) :=
  PointedFiberComparison.map (p.app n) (q.app n) (a.app n) (b.app n)
    (congrArg (fun f => f.app n) h)

omit hp hq in
lemma level_ι (n : ℕ) : level p q a b h n ≫ pointedFiberι (q.app n) =
    pointedFiberι (p.app n) ≫ a.app n := PointedFiberComparison.map_ι _ _ _ _ _

def sequenceMap : KanSequence.Hom ((OmegaSpectrum.sequenceHom p).fiber hp)
    ((OmegaSpectrum.sequenceHom q).fiber hq) where
  app := level p q a b h
  comm n := by
    apply pointedFiber_hom_ext (q.app (n + 1))
    change (PointedSimplicialSet.circle.{u} ◁ level p q a b h n ≫
      (OmegaSpectrum.sequenceHom q).fiberSigma n) ≫ pointedFiberι (q.app (n + 1)) =
      ((OmegaSpectrum.sequenceHom p).fiberSigma n ≫ level p q a b h (n + 1)) ≫
        pointedFiberι (q.app (n + 1))
    have hpι : (OmegaSpectrum.sequenceHom p).fiberSigma n ≫
        pointedFiberι (p.app (n + 1)) =
        PointedSimplicialSet.circle.{u} ◁ pointedFiberι (p.app n) ≫ X.sigma n :=
      pointedFiberLiftOfZero_ι _ _ _
    have hqι : (OmegaSpectrum.sequenceHom q).fiberSigma n ≫
        pointedFiberι (q.app (n + 1)) =
        PointedSimplicialSet.circle.{u} ◁ pointedFiberι (q.app n) ≫ X'.sigma n :=
      pointedFiberLiftOfZero_ι _ _ _
    rw [Category.assoc, hqι, ← Category.assoc, ← whiskerLeft_comp, level_ι,
      whiskerLeft_comp, Category.assoc, a.comm n]
    rw [Category.assoc, level_ι]
    simpa only [Category.assoc] using
      (congrArg (fun t => t ≫ a.app (n + 1)) hpι).symm


end SerrePositivity.KST.LocalizingInvariants.FibrationFiberComparison
