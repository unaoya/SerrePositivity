module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumMappingIntervalPath

/-!
概要：指定 BF 合成三角形を、Sp の辺の関手圏の同じ合成三角形と合成式へ移す。
方針：二次までの宇宙持ち上げと coherent 区間比較を同じ二単体に適用する。
規約：三角形の充填を選び直さない。使われ方：rightDifference の実三角形の保持。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath

local instance intervalTriangleCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y : OmegaSpectrum.{u}} {h f g : X ⟶ Y}
  {H : (mappingSpace X Y).Edge (vertexOfHom h) (vertexOfHom f)}
  {e : (mappingSpace X Y).Edge (vertexOfHom f) (vertexOfHom g)}
  {V : (mappingSpace X Y).Edge (vertexOfHom h) (vertexOfHom g)}
  (t : SSet.Edge.CompStruct H e V)

def intervalComposition : SSet.Edge.CompStruct (intervalEdge H) (intervalEdge e)
    (intervalEdge V) := by
  let T := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedCompStruct.{u, u + 1} t.toTruncated).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y))
  let liftEdge (k l : X ⟶ Y)
      (P : (mappingSpace X Y).Edge (vertexOfHom k) (vertexOfHom l)) :=
    (SSet.Edge.ofTruncated (X := (SSet.uliftFunctor.{u + 1, u}).obj (mappingSpace X Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge P.toTruncated)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y)
  let U : SSet.Edge.CompStruct (liftEdge h f H) (liftEdge f g e) (liftEdge h g V) :=
    SSet.Edge.CompStruct.ofTruncated T
  exact U.ofEq rfl rfl rfl

def arrowComposition : SSet.Edge.CompStruct (arrowEdge H) (arrowEdge e) (arrowEdge V) :=
  (intervalComposition t).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _)

lemma arrowComposition_simplex : (arrowComposition t).simplex =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _).app (Opposite.op ⦋2⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y).app (Opposite.op ⦋2⦌)
        (ULift.up t.simplex)) := rfl

def arrowHom {k l : X ⟶ Y}
    (P : (mappingSpace X Y).Edge (vertexOfHom k) (vertexOfHom l)) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge l).edge) :=
  Truncated.HomotopyCategory.homMk (arrowEdge P).toTruncated

include t in
lemma arrowHom_comp : arrowHom H ≫ arrowHom e = arrowHom V :=
  Truncated.HomotopyCategory.homMk_comp_homMk (arrowComposition t).toTruncated

end SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath
