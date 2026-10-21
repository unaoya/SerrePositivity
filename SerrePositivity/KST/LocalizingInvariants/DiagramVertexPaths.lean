module

public import SerrePositivity.KST.LocalizingInvariants.EquivalencePathFamily
public import SerrePositivity.InfinityCategories.Core.VertexDiscrete
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

/-!
概要：図式の全頂点に指定した可逆 path を、図式全体の可逆 path へ延長する。
方針：頂点の離散包含の単射性と、可逆 path の始点評価の自明 Kan 性を使う。
規約：頂点で選んだ実際の path を保持。使われ方：元の積同値による正方形の全図式移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {K X : SSet.{u}} [Quasicategory X]

structure DiagramVertexPaths (F : K ⟶ X) where
  path : K _⦋0⦌ → (equivalencePath X) _⦋0⦌
  source (v) : (equivalencePathEndpoint X 0).app (Opposite.op ⦋0⦌) (path v) =
    F.app (Opposite.op ⦋0⦌) v

namespace DiagramVertexPaths
variable {F : K ⟶ X} (d : DiagramVertexPaths F)

structure Extension where
  family : K ⟶ equivalencePath X
  source : family ≫ equivalencePathEndpoint X 0 = F
  vertices : vertexDiscreteι K ≫ family = vertexDiscreteMap d.path

lemma extension_nonempty : Nonempty (Extension d) := by
  have he := vertexDiscreteMap_comp (equivalencePathEndpoint X 0) F d.path d.source
  let sq : CommSq (vertexDiscreteMap d.path) (vertexDiscreteι K)
      (equivalencePathEndpoint X 0) F := ⟨he⟩
  have : HasLiftingProperty (vertexDiscreteι K) (equivalencePathEndpoint X 0) :=
    TrivialKanFibration.mem (p := equivalencePathEndpoint X 0) (vertexDiscreteι K) inferInstance
  exact ⟨⟨sq.lift, sq.fac_right, sq.fac_left⟩⟩

def extension : Extension d := (extension_nonempty d).some

namespace Extension
variable {d} (w : Extension d)

omit [Quasicategory X] in
lemma family_vertex (v : K _⦋0⦌) :
    w.family.app (Opposite.op ⦋0⦌) v = d.path v := by
  have h := congrArg (fun f : vertexDiscrete K ⟶ equivalencePath X =>
    f.app (Opposite.op ⦋0⦌) v) w.vertices
  change w.family.app (Opposite.op ⦋0⦌) (PinchedHom.constant v 0) =
    PinchedHom.constant (d.path v) 0 at h
  simpa only [pinchedConstant_zero] using h

def target : K ⟶ X := w.family ≫ equivalencePathEndpoint X 1

lemma target_vertex (v : K _⦋0⦌) : w.target.app (Opposite.op ⦋0⦌) v =
    (equivalencePathEndpoint X 1).app (Opposite.op ⦋0⦌) (d.path v) := by
  change (equivalencePathEndpoint X 1).app _ (w.family.app _ v) = _
  rw [w.family_vertex]

def comparison : FunctorIso F w.target :=
  (eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) w.source)).symm ≪≫
    equivalencePathFamilyIso w.family

end Extension
end DiagramVertexPaths

lemma DiagramVertexPaths.Extension.target_isPullback
    {S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    {d : DiagramVertexPaths S} (w : d.Extension) (hS : IsPullbackSquare S) :
    IsPullbackSquare w.target := hS.of_functorIso w.comparison

end SerrePositivity.KST.LocalizingInvariants
