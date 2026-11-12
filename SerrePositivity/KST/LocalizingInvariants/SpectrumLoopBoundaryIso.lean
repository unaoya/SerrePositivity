module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumLoopFiberDiagram
public import SerrePositivity.KST.LocalizingInvariants.NativeFiberBoundaryIso

/-!
概要：元の全 loop 四角形の接続射は、全整数次数の自然な群同型である。
方針：零成分の π の消滅と実 fiber 長完全列から全単射性を導き、全図式の自然性を使う。
規約：対象別の次数同型を自然性の代わりに入力しない。
使われ方：native loop と円 cotensor の整数 π 関手の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumLoop

lemma totalGroup_subsingleton (x : hoFunctor.obj diagrams.{u}) (j : ℤ) :
    Subsingleton (NativeFiber.group (fiberDiagramAt x.as.as).triangle 1 0 j) :=
  SpectrumHo.piFunctor_subsingleton_of_isZero _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x.as.as).2.1 j

lemma boundary_bijective (x : hoFunctor.obj diagrams.{u}) (j : ℤ) :
    Function.Bijective (NativeFiber.boundary (fiberDiagramAt x.as.as).triangle
      (fiberDiagramAt x.as.as).isFiber j) :=
  NativeFiber.boundary_bijective_of_totalGroups _ _ j
    (totalGroup_subsingleton x j) (totalGroup_subsingleton x (j + 1))

def boundaryGroupIso (x : hoFunctor.obj diagrams.{u}) (j : ℤ) :
    NativeFiber.group (fiberDiagramAt x.as.as).triangle 1 1 (j + 1) ≅
      NativeFiber.group (fiberDiagramAt x.as.as).triangle 0 0 j :=
  (MulEquiv.ofBijective
    (NativeFiber.boundary (fiberDiagramAt x.as.as).triangle (fiberDiagramAt x.as.as).isFiber j)
    (boundary_bijective x j)).toCommGrpIso

set_option maxHeartbeats 800000 in
def boundaryNatIso (j : ℤ) :
    (fiberDiagrams.{u} ⋙ FiberDiagram.vertex 1 1) ⋙ SpectrumHo.piFunctor (j + 1) ≅
      (fiberDiagrams.{u} ⋙ FiberDiagram.vertex 0 0) ⋙ SpectrumHo.piFunctor j :=
  NatIso.ofComponents (fun x => by
    change NativeFiber.group (fiberDiagramAt x.as.as).triangle 1 1 (j + 1) ≅
      NativeFiber.group (fiberDiagramAt x.as.as).triangle 0 0 j
    exact boundaryGroupIso x j) (by
      intro x y f
      apply ConcreteCategory.hom_ext
      intro a
      exact (FiberDiagram.boundary_natural (fiberDiagrams.map f) j a).symm)

def piShiftIso (j : ℤ) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0)).toFunctor ⋙ SpectrumHo.piFunctor j ≅
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1)).toFunctor ⋙
        SpectrumHo.piFunctor (j + 1) :=
  ((Functor.isoWhiskerRight (vertexIso 1 1) (SpectrumHo.piFunctor (j + 1))).symm ≪≫
    boundaryNatIso j ≪≫ Functor.isoWhiskerRight (vertexIso 0 0) (SpectrumHo.piFunctor j)).symm

end SerrePositivity.KST.LocalizingInvariants.SpectrumLoop
