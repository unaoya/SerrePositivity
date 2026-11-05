module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Exact.ExactKernelStableClosure

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
namespace SerrePositivity.InfinityCategories.Stable.Exact
open SerrePositivity.KST.LocalizingInvariants

def exactKernel {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) : Set (A.obj _⦋0⦌) :=
  {x | IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) x)}

lemma exactKernel_stableClosure {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) :
    {x | StableVertexClosure (_root_.SerrePositivity.InfinityCategories.Stable.Exact.exactKernel F) x} = _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactKernel F := by
  ext x
  constructor
  · intro hx
    exact kills_stableVertexClosure F.hom (_root_.SerrePositivity.InfinityCategories.Stable.Exact.exactKernel F) (fun _ hy => hy) hx
  · exact StableVertexClosure.of_mem

lemma invertedEdges_eq_cofiber_exactKernel {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) :
    invertedEdges F.hom = cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.Stable.Exact.exactKernel F) := by
  ext e
  constructor
  · intro he
    let c := chosenCofiberSquare (edgeOfSimplex e)
    have hz := (c.map_isInvertible_iff_zero F.hom).mp he
    exact ⟨c, c.cofiber, hz, ⟨Iso.refl _⟩⟩
  · intro he
    exact inverts_cofiberLocalizingEdges_of_kills F.hom (_root_.SerrePositivity.InfinityCategories.Stable.Exact.exactKernel F) (fun _ hx => hx) he

end SerrePositivity.InfinityCategories.Stable.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactKernel (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactKernel := _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactKernel

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactKernel_stableClosure := _root_.SerrePositivity.InfinityCategories.Stable.Exact.exactKernel_stableClosure

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.invertedEdges_eq_cofiber_exactKernel := _root_.SerrePositivity.InfinityCategories.Stable.Exact.invertedEdges_eq_cofiber_exactKernel
