module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramModelGroups

/-!
概要：元の接続射が使用する全正方形の同型を、fiber 図式の実際の正規化として保持する。
方針：三項群比較と同じ選択を使い、任意の図式の射を全 h Fun 内で共役する。
規約：右辺の二頂点が固定されるとは仮定しない。使われ方：元の接続射への自然性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

local instance normalizationSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance normalizationNerveQuasicategory :
    Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

def normalized (D : FiberDiagram.{u}) : FiberDiagram.{u} where
  triangle := (FiberModel.homotopyFiberSquare (NativeFiber.rightMap D.triangle)).toZeroTriangle
  isFiber := (FiberModel.homotopyFiberSquare (NativeFiber.rightMap D.triangle)).isPullback

def normalizationDiagramIso (D : FiberDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso D.triangle.square (normalized D).triangle.square :=
  (FiberComparison.relativeFunctorIso
    (NativeFiber.asFiberSquare D.triangle D.isFiber)
    (FiberModel.homotopyFiberSquare (NativeFiber.rightMap D.triangle))).iso

def normalization (D : FiberDiagram.{u}) : D ≅ normalized D where
  hom := (normalizationDiagramIso D).hom
  inv := (normalizationDiagramIso D).inv
  hom_inv_id := (normalizationDiagramIso D).hom_inv_id
  inv_hom_id := (normalizationDiagramIso D).inv_hom_id

def normalizedHom {D E : FiberDiagram.{u}} (f : D ⟶ E) : normalized D ⟶ normalized E :=
  (normalization D).inv ≫ f ≫ (normalization E).hom

def normalizationFunctor : FiberDiagram.{u} ⥤ FiberDiagram.{u} where
  obj := normalized
  map := normalizedHom
  map_id D := by simp only [normalizedHom, Category.id_comp, Iso.inv_hom_id]
  map_comp {D E F} f g := by
    simp only [normalizedHom, Category.assoc, Iso.hom_inv_id_assoc]

def normalizationNatIso : 𝟭 FiberDiagram.{u} ≅ normalizationFunctor :=
  NatIso.ofComponents normalization (by
    intro D E f
    change f ≫ (normalization E).hom = (normalization D).hom ≫ normalizedHom f
    simp only [normalizedHom, Iso.hom_inv_id_assoc])

lemma normalizedHom_vertex {D E : FiberDiagram.{u}} (f : D ⟶ E) (i j : Fin 2) :
    (vertex i j).map (normalizedHom f) =
      (vertex i j).map (normalization D).inv ≫
        (vertex i j).map f ≫ (vertex i j).map (normalization E).hom := by
  simp only [normalizedHom, Functor.map_comp]

lemma normalization_fiber (D : FiberDiagram.{u}) :
    (vertex 0 0).map (normalization D).hom ≫
        (FiberModel.fiberObjectIso (NativeFiber.rightMap D.triangle)).hom =
      (FiberPi.fiberIso (NativeFiber.rightMap D.triangle)
        (NativeFiber.asFiberSquare D.triangle D.isFiber)).hom := by
  rfl

lemma normalization_total (D : FiberDiagram.{u}) :
    (vertex 1 0).map (normalization D).hom ≫
        (FiberModel.totalObjectIso (NativeFiber.rightMap D.triangle)).hom =
      (FiberPi.totalIso (NativeFiber.rightMap D.triangle)
        (NativeFiber.asFiberSquare D.triangle D.isFiber)).hom := by
  rfl

lemma normalization_base (D : FiberDiagram.{u}) :
    (vertex 1 1).map (normalization D).hom ≫
        (FiberModel.baseObjectIso (NativeFiber.rightMap D.triangle)).hom =
      (FiberPi.baseIso (NativeFiber.rightMap D.triangle)
        (NativeFiber.asFiberSquare D.triangle D.isFiber)).hom := by
  rfl

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
