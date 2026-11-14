module

public import SerrePositivity.KST.LocalizingInvariants.FiberSequenceComparison
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquareArrows
public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyComparison

/-!
概要：同じ BF 射の任意の fiber 四角形の三対象を元の BF 三対象と比較する。
方針：全図式の短複体同型と元の BF 頂点の同定を合成し、整数 π 関手で写す。
規約：下辺と右辺を同時に保つ。使われ方：K-5 の一般 fiber 列の長完全列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberPi

local instance fiberPiSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance fiberPiHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

variable {E B : OmegaSpectrum.{u}} (f : E ⟶ B)
  (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated)

def comparison := FiberComparison.fiberShortComplexIso (X := Sp.{u}) s
  (FiberModel.homotopyFiberSquare f)

def fiberIso : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex s.square 0 0 ≅ SpectrumHo.obj (homotopyFiber f) :=
  ShortComplex.π₁.mapIso (comparison f s) ≪≫ FiberModel.fiberObjectIso f

def totalIso : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex s.square 1 0 ≅ SpectrumHo.obj E :=
  ShortComplex.π₂.mapIso (comparison f s) ≪≫ FiberModel.totalObjectIso f

def baseIso : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex s.square 1 1 ≅ SpectrumHo.obj B :=
  ShortComplex.π₃.mapIso (comparison f s) ≪≫ FiberModel.baseObjectIso f

lemma bottom_naturality : (fiberIso f s).hom ≫ SpectrumHo.hom (homotopyFiberInclusion f) =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom s.square ≫ (totalIso f s).hom := by
  change ((comparison f s).hom.τ₁ ≫ (FiberModel.fiberObjectIso f).hom) ≫ _ =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom s.square ≫ ((comparison f s).hom.τ₂ ≫ (FiberModel.totalObjectIso f).hom)
  have hc := (comparison f s).hom.comm₁₂
  change (comparison f s).hom.τ₁ ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (FiberModel.homotopyFiberSquare f).square =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom s.square ≫ (comparison f s).hom.τ₂ at hc
  rw [Category.assoc, FiberModel.bottom_naturality]
  simpa only [Category.assoc] using
    congrArg (fun m ↦ m ≫ (FiberModel.totalObjectIso f).hom) hc

lemma right_naturality : (totalIso f s).hom ≫ SpectrumHo.hom f =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight s.square ≫ (baseIso f s).hom := by
  change ((comparison f s).hom.τ₂ ≫ (FiberModel.totalObjectIso f).hom) ≫ _ =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight s.square ≫ ((comparison f s).hom.τ₃ ≫ (FiberModel.baseObjectIso f).hom)
  have hc := (comparison f s).hom.comm₂₃
  change (comparison f s).hom.τ₂ ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight (FiberModel.homotopyFiberSquare f).square =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight s.square ≫ (comparison f s).hom.τ₃ at hc
  rw [Category.assoc, FiberModel.right_naturality]
  simpa only [Category.assoc] using
    congrArg (fun m ↦ m ≫ (FiberModel.baseObjectIso f).hom) hc

def fiberGroupIso (j : ℤ) :
    (SpectrumHo.piFunctor j).obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex s.square 0 0) ≅
      CommGrpCat.of (homotopyGroup (homotopyFiber f) j) :=
  (SpectrumHo.piFunctor j).mapIso (fiberIso f s) ≪≫ SpectrumHo.piComparison _ j

def totalGroupIso (j : ℤ) :
    (SpectrumHo.piFunctor j).obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex s.square 1 0) ≅
      CommGrpCat.of (homotopyGroup E j) :=
  (SpectrumHo.piFunctor j).mapIso (totalIso f s) ≪≫ SpectrumHo.piComparison _ j

def baseGroupIso (j : ℤ) :
    (SpectrumHo.piFunctor j).obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex s.square 1 1) ≅
      CommGrpCat.of (homotopyGroup B j) :=
  (SpectrumHo.piFunctor j).mapIso (baseIso f s) ≪≫ SpectrumHo.piComparison _ j

/-- 対象同型と元の BF π 比較を合成した後も、元の射の自然性が保たれる。 -/
lemma group_naturality {x y : hoFunctor.obj Sp.{u}} {X Y : OmegaSpectrum.{u}}
    (m : x ⟶ y) (g : X ⟶ Y) (a : x ≅ SpectrumHo.obj X) (b : y ≅ SpectrumHo.obj Y)
    (h : a.hom ≫ SpectrumHo.hom g = m ≫ b.hom) (j : ℤ) :
    (SpectrumHo.piFunctor j).map m ≫
        ((SpectrumHo.piFunctor j).mapIso b ≪≫ SpectrumHo.piComparison Y j).hom =
      ((SpectrumHo.piFunctor j).mapIso a ≪≫ SpectrumHo.piComparison X j).hom ≫
        CommGrpCat.ofHom (homotopyMap g j) := by
  change (SpectrumHo.piFunctor j).map m ≫
    ((SpectrumHo.piFunctor j).map b.hom ≫ (SpectrumHo.piComparison Y j).hom) = _
  rw [← Category.assoc, ← Functor.map_comp, ← h, Functor.map_comp, Category.assoc,
    SpectrumHo.piComparison_naturality]
  rfl

lemma bottom_group_naturality (j : ℤ) :
    (SpectrumHo.piFunctor j).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom s.square) ≫ (totalGroupIso f s j).hom =
      (fiberGroupIso f s j).hom ≫ CommGrpCat.ofHom (homotopyMap (homotopyFiberInclusion f) j) :=
  group_naturality _ _ (fiberIso f s) (totalIso f s) (bottom_naturality f s) j

lemma right_group_naturality (j : ℤ) :
    (SpectrumHo.piFunctor j).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight s.square) ≫ (baseGroupIso f s j).hom =
      (totalGroupIso f s j).hom ≫ CommGrpCat.ofHom (homotopyMap f j) :=
  group_naturality _ _ (totalIso f s) (baseIso f s) (right_naturality f s) j

end SerrePositivity.KST.LocalizingInvariants.FiberPi
