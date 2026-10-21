module

public import SerrePositivity.KST.LocalizingInvariants.ExactKernelStableClosure

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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def exactKernel {A B : StableCategory.{u}} (F : ExactMap A B) : Set (A.obj _⦋0⦌) :=
  {x | IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) x)}

lemma exactKernel_stableClosure {A B : StableCategory.{u}} (F : ExactMap A B) :
    {x | StableVertexClosure (exactKernel F) x} = exactKernel F := by
  ext x
  constructor
  · intro hx
    exact kills_stableVertexClosure F.hom (exactKernel F) (fun _ hy => hy) hx
  · exact StableVertexClosure.of_mem

lemma invertedEdges_eq_cofiber_exactKernel {A B : StableCategory.{u}} (F : ExactMap A B) :
    invertedEdges F.hom = cofiberLocalizingEdges (exactKernel F) := by
  ext e
  constructor
  · intro he
    let c := chosenCofiberSquare (edgeOfSimplex e)
    have hz := (c.map_isInvertible_iff_zero F.hom).mp he
    exact ⟨c, c.cofiber, hz, ⟨Iso.refl _⟩⟩
  · intro he
    exact inverts_cofiberLocalizingEdges_of_kills F.hom (exactKernel F) (fun _ hx => hx) he

end SerrePositivity.KST.LocalizingInvariants
