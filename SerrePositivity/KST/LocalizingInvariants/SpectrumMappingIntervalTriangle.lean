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
  let T := (uliftTruncatedCompStruct.{u, u + 1} t.toTruncated).map
    ((truncation 2).map (coherentHomIntervalComparison X Y))
  let liftEdge (k l : X ⟶ Y)
      (P : (mappingSpace X Y).Edge (vertexOfHom k) (vertexOfHom l)) :=
    (SSet.Edge.ofTruncated (X := (SSet.uliftFunctor.{u + 1, u}).obj (mappingSpace X Y))
      (uliftTruncatedEdge P.toTruncated)).map (coherentHomIntervalComparison X Y)
  let U : SSet.Edge.CompStruct (liftEdge h f H) (liftEdge f g e) (liftEdge h g V) :=
    SSet.Edge.CompStruct.ofTruncated T
  exact U.ofEq rfl rfl rfl

def arrowComposition : SSet.Edge.CompStruct (arrowEdge H) (arrowEdge e) (arrowEdge V) :=
  (intervalComposition t).map (vertexFiberι _ _)

lemma arrowComposition_simplex : (arrowComposition t).simplex =
    (vertexFiberι _ _).app (Opposite.op ⦋2⦌)
      ((coherentHomIntervalComparison X Y).app (Opposite.op ⦋2⦌)
        (ULift.up t.simplex)) := rfl

def arrowHom {k l : X ⟶ Y}
    (P : (mappingSpace X Y).Edge (vertexOfHom k) (vertexOfHom l)) :
    FunctorHom (SSet.yonedaEquiv.symm (coherentNerveEdge k).edge)
      (SSet.yonedaEquiv.symm (coherentNerveEdge l).edge) :=
  Truncated.HomotopyCategory.homMk (arrowEdge P).toTruncated

include t in
lemma arrowHom_comp : arrowHom H ≫ arrowHom e = arrowHom V :=
  Truncated.HomotopyCategory.homMk_comp_homMk (arrowComposition t).toTruncated

end SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath
