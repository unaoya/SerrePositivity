module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberSquareLeg
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.SquareHomotopyCategory

/-!
概要：BF fiber 四角形の三対象と二辺を、元の BF 射の類に同時に同定する。
方針：辺の端点の等号による輸送と、下辺の類の照合を合成する。
規約：比較の対象等号も明示する。使われ方：K-5 の長完全列の三項同時移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

local instance fiberArrowsSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 端点の表示が異なる同じ辺の類を、等号の射と可換する式で比較する。 -/
lemma homMk_transport {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (e' : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y')
    (hx : x = x') (hy : y = y') (he : e.edge = e'.edge) :
    SSet.Truncated.HomotopyCategory.homMk e ≫
        eqToHom (congrArg SSet.HomotopyCategory.mk hy) =
      eqToHom (congrArg SSet.HomotopyCategory.mk hx) ≫
        SSet.Truncated.HomotopyCategory.homMk e' := by
  subst x' y'
  have h : e = e' := SSet.Truncated.Edge.ext he
  subst e'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

variable {E B : OmegaSpectrum.{u}} (f : E ⟶ B)

lemma homotopyFiberSquare_source_vertex :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (homotopyFiberSquare f).square 1 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex E := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source, (homotopyFiberSquare f).right_edge]
  exact (congrArg (fun v : Sp.{u} _⦋1⦌ ↦ Sp.{u}.δ 1 v)
    (SSet.yonedaEquiv.apply_symm_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).src_eq

lemma homotopyFiberSquare_target_vertex :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (homotopyFiberSquare f).square 1 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex B := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target, (homotopyFiberSquare f).right_edge]
  exact (congrArg (fun v : Sp.{u} _⦋1⦌ ↦ Sp.{u}.δ 0 v)
    (SSet.yonedaEquiv.apply_symm_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).tgt_eq

def fiberObjectIso : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (homotopyFiberSquare f).square 0 0 ≅
    SpectrumHo.obj (homotopyFiber f) :=
  eqToIso (congrArg SSet.HomotopyCategory.mk (homotopyFiberSquare_vertex f))

def totalObjectIso : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (homotopyFiberSquare f).square 1 0 ≅ SpectrumHo.obj E :=
  eqToIso (congrArg SSet.HomotopyCategory.mk (homotopyFiberSquare_source_vertex f))

def baseObjectIso : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (homotopyFiberSquare f).square 1 1 ≅ SpectrumHo.obj B :=
  eqToIso (congrArg SSet.HomotopyCategory.mk (homotopyFiberSquare_target_vertex f))

/-- 三対象の比較は元の homotopyFiberInclusion と下辺の類を可換させる。 -/
lemma bottom_naturality : (fiberObjectIso f).hom ≫
      SpectrumHo.hom (homotopyFiberInclusion f) =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (homotopyFiberSquare f).square ≫ (totalObjectIso f).hom := by
  have h := homMk_transport (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (homotopyFiberSquare f).square)
    (homotopyFiberSquareBottom f).toTruncated
    (homotopyFiberSquare_vertex f) (homotopyFiberSquare_source_vertex f)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge (homotopyFiberSquare f).square)
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (homotopyFiberSquare f).square ≫ (totalObjectIso f).hom =
    (fiberObjectIso f).hom ≫
      SSet.Truncated.HomotopyCategory.homMk (homotopyFiberSquareBottom f).toTruncated at h
  exact (h.trans (congrArg ((fiberObjectIso f).hom ≫ ·)
    (homotopyFiberSquare_bottom_hom f))).symm

/-- 同じ三対象の比較は右辺と元の BF 射の類も可換させる。 -/
lemma right_naturality : (totalObjectIso f).hom ≫ SpectrumHo.hom f =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight (homotopyFiberSquare f).square ≫ (baseObjectIso f).hom := by
  have he : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (homotopyFiberSquare f).square).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge, (homotopyFiberSquare f).right_edge]
    exact SSet.yonedaEquiv.apply_symm_apply _
  exact (homMk_transport (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (homotopyFiberSquare f).square)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated (homotopyFiberSquare_source_vertex f)
    (homotopyFiberSquare_target_vertex f) he).symm

end SerrePositivity.KST.LocalizingInvariants.FiberModel
