module

public import SerrePositivity.KST.LocalizingInvariants.RawFiberCoherentCube
public import SerrePositivity.KST.LocalizingInvariants.SliceConeComparison
public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomClass

/-!
概要：実 fiber の全錐比較を h Fun の射として保持し、頂点と底の元の射へ戻す。
方針：同じ cube の辺の類を取り、頂点辺と底の全区間の等号を使う。
規約：元の BF 比較と元の cospan prism。使われ方：置換比較の共役による全図式移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.LocalizingInvariants.RawFiberComparison

local instance rawCubeHomSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  [hp : ∀ n, Fibration (p.app n).right] [hq : ∀ n, Fibration (q.app n).right]
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def cubeHom : FunctorHom (X := Sp.{u}) (FiberModel.infinityCone p).val
    (FiberModel.infinityCone q).val :=
  Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (cube p q a b h))

lemma cubeHom_apex :
    Arrow.mk (functorHomEvaluate (X := Sp.{u}) (cubeHom p q a b h) (joinApexVertex _)) =
      Arrow.mk (SpectrumHo.hom (map p q a b h)) := by
  rw [cubeHom, functorHomEvaluate_homotopy]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact cube_apex p q a b h

def diagramHomotopy := F2.prismHomotopy (F2.strictCoherentNatTransMap (diagramMap p q a b h))
  (F2.strictCoherentNatTransMap_zero _) (F2.strictCoherentNatTransMap_one _)

lemma cubeHom_base : Arrow.mk (homPre (joinInr Δ[0] _) (cubeHom p q a b h)) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (diagramHomotopy p q a b h))) := by
  unfold cubeHom homPre
  rw [homMk_functorEdge_precomp]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  change SSet.yonedaEquiv (MonoidalClosed.curry
    ((joinInr Δ[0] _ ▷ Δ[1]) ≫ (cube p q a b h).h)) = _
  rw [cube_base]
  rfl

end SerrePositivity.KST.LocalizingInvariants.RawFiberComparison
