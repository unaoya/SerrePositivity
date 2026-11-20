module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.ExactKernelStableClosure

/-!
概要：完全関手の真の核は安定閉包で変わらず、核に cofiber を持つ辺は反転辺と一致する。
方針：核の頂点を直接使い、cofiber の像の零性と元の辺の可逆性を比較する。
規約：核を表す包含の存在は仮定しない。使われ方：矢印圏上の点ごとの元の分母。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
open _root_.SerrePositivity.KST.LocalizingInvariants

def exactKernel {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) : Set (A.obj _⦋0⦌) :=
  {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) x)}

lemma exactKernel_stableClosure {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactKernel F) x} = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactKernel F := by
  ext x
  constructor
  · intro hx
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kills_stableVertexClosure F.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactKernel F) (fun _ hy => hy) hx
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem

lemma invertedEdges_eq_cofiber_exactKernel {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F.hom = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactKernel F) := by
  ext e
  constructor
  · intro he
    let c := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e)
    have hz := (c.map_isInvertible_iff_zero F.hom).mp he
    exact ⟨c, c.cofiber, hz, ⟨Iso.refl _⟩⟩
  · intro he
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.inverts_cofiberLocalizingEdges_of_kills F.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactKernel F) (fun _ hx => hx) he

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
