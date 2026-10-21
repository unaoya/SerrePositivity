module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramModelEquality
public import SerrePositivity.KST.LocalizingInvariants.ArrowTransportNaturality

/-!
概要：元の fiber 図式の整数 π と、同じ模型 fiber 群との比較の自然性を示す。
方針：模型頂点の等号同型と全比較の一致を使い、同じ正規化で元の頂点へ戻す。
規約：接続射と同じ fiberGroupIso を保持。使われ方：接続射の一般自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

local instance fiberGroupNaturalityCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance fiberGroupNaturalityNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

variable {D E : FiberDiagram.{u}} (f : D ⟶ E)

def normalizedFiberGroupIso (D : FiberDiagram.{u}) (j : ℤ) :
    (SpectrumHo.piFunctor j).obj ((vertex 0 0).obj (normalized D)) ≅
      CommGrpCat.of (modelGroup D j) :=
  (SpectrumHo.piFunctor j).mapIso
    (FiberModel.fiberObjectIso (NativeFiber.rightMap D.triangle)) ≪≫
      SpectrumHo.piComparison (homotopyFiber (NativeFiber.rightMap D.triangle)) j

def fiberGroupIso (D : FiberDiagram.{u}) (j : ℤ) :
    (SpectrumHo.piFunctor j).obj ((vertex 0 0).obj D) ≅ CommGrpCat.of (modelGroup D j) :=
  FiberPi.fiberGroupIso (NativeFiber.rightMap D.triangle)
    (NativeFiber.asFiberSquare D.triangle D.isFiber) j

lemma normalizedFiberGroupIso_hom (D : FiberDiagram.{u}) (j : ℤ) :
    (normalizedFiberGroupIso D j).hom =
      (SpectrumHo.piFunctor j).map
        (FiberModel.fiberObjectIso (NativeFiber.rightMap D.triangle)).hom ≫
          (SpectrumHo.piComparison (homotopyFiber (NativeFiber.rightMap D.triangle)) j).hom :=
  rfl

lemma normalized_fiber_vertex (D : FiberDiagram.{u}) : (vertex 0 0).obj (normalized D) =
    SpectrumHo.obj (homotopyFiber (NativeFiber.rightMap D.triangle)) :=
  congrArg HomotopyCategory.mk (FiberModel.homotopyFiberSquare_vertex _)

lemma normalizedFiberGroupIso_naturality (j : ℤ) :
    (SpectrumHo.piFunctor j).map
      ((vertex 0 0).map (X := normalized D) (Y := normalized E) (normalizedHom f)) ≫
      (normalizedFiberGroupIso E j).hom =
    (normalizedFiberGroupIso D j).hom ≫ CommGrpCat.ofHom (modelGroupMap f j) := by
  let p := NativeFiber.rightMap D.triangle
  let q := NativeFiber.rightMap E.triangle
  let F := SpectrumHo.piFunctor j
  have he := arrow_eqToHom_map_naturality F
    ((vertex 0 0).map (X := normalized D) (Y := normalized E) (normalizedHom f))
    ((SpectrumHo.piComparison (homotopyFiber p) j).hom ≫
      CommGrpCat.ofHom (modelGroupMap f j) ≫
      (SpectrumHo.piComparison (homotopyFiber q) j).inv)
    (normalized_fiber_vertex D) (normalized_fiber_vertex E)
    (normalizedHom_fiber_pi f j)
  change F.map ((vertex 0 0).map (X := normalized D) (Y := normalized E)
      (normalizedHom f)) ≫ F.map (FiberModel.fiberObjectIso q).hom =
    F.map (FiberModel.fiberObjectIso p).hom ≫
      ((SpectrumHo.piComparison (homotopyFiber p) j).hom ≫
        CommGrpCat.ofHom (modelGroupMap f j) ≫
        (SpectrumHo.piComparison (homotopyFiber q) j).inv) at he
  rw [normalizedFiberGroupIso_hom, normalizedFiberGroupIso_hom, ← Category.assoc, he]
  dsimp only [p, q, F]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma fiberGroupIso_normalization (D : FiberDiagram.{u}) (j : ℤ) :
    (fiberGroupIso D j).hom =
      (SpectrumHo.piFunctor j).map ((vertex 0 0).map (normalization D).hom) ≫
        (normalizedFiberGroupIso D j).hom := by
  change (SpectrumHo.piFunctor j).map
      (FiberPi.fiberIso (NativeFiber.rightMap D.triangle)
        (NativeFiber.asFiberSquare D.triangle D.isFiber)).hom ≫ _ = _
  rw [← normalization_fiber, Functor.map_comp, Category.assoc]
  rfl

lemma fiberGroupIso_naturality (j : ℤ) :
    (SpectrumHo.piFunctor j).map ((vertex 0 0).map f) ≫ (fiberGroupIso E j).hom =
      (fiberGroupIso D j).hom ≫ CommGrpCat.ofHom (modelGroupMap f j) := by
  let F := vertex 0 0 ⋙ SpectrumHo.piFunctor j
  have hn := congrArg F.map (normalizationNatIso.hom.naturality f)
  simp only [Functor.map_comp] at hn
  change (SpectrumHo.piFunctor j).map ((vertex 0 0).map f) ≫
      (SpectrumHo.piFunctor j).map ((vertex 0 0).map (normalization E).hom) =
    (SpectrumHo.piFunctor j).map ((vertex 0 0).map (normalization D).hom) ≫
      (SpectrumHo.piFunctor j).map
      ((vertex 0 0).map (X := normalized D) (Y := normalized E) (normalizedHom f)) at hn
  rw [fiberGroupIso_normalization, fiberGroupIso_normalization]
  rw [← Category.assoc, hn, Category.assoc, normalizedFiberGroupIso_naturality]
  simp only [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
