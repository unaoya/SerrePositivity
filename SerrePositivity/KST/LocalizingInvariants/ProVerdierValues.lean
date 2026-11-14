module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.VerdierDiagramCategory
public import SerrePositivity.KST.LocalizingInvariants.ProFiberSequence

/-!
概要：局所化不変量は全図式の比較を持つ Verdier 図式の塔を実 fiber 図式の塔へ送る。
方針：元の単体的関手を正方形全体に後合成し、関手 ∞ 圏の射と合成則も写す。
規約：像の fiber 性は局所化不変性から導く。使われ方：pro 長完全列と抽象 pro 切除。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)

def fiberDiagramFunctor : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u} ⥤ FiberDiagram.{u} where
  obj D := ⟨hΦ.fiberTriangle D, hΦ.fiberTriangle_isFiber D⟩
  map f := homPost Φ f
  map_id D := homPost_id Φ D.square
  map_comp f g := homPost_homComp Φ f g

def proFiberSequence (D : ProExcision.Tower _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) : ProFiberSequence.{u} :=
  D.map hΦ.fiberDiagramFunctor

lemma proFiberSequence_square (D : ProExcision.Tower _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (n : ℕ) :
    ((hΦ.proFiberSequence D).obj n).triangle.square = (D.obj n).square ≫ Φ := rfl

lemma proFiberSequence_inclusion (D : ProExcision.Tower _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (n : ℕ) :
    (ProFiberSequence.inclusion (hΦ.proFiberSequence D)).app n =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom ((D.obj n).square ≫ Φ) := rfl

lemma proFiberSequence_projection (D : ProExcision.Tower _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (n : ℕ) :
    (ProFiberSequence.projection (hΦ.proFiberSequence D)).app n =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight ((D.obj n).square ≫ Φ) := rfl

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
