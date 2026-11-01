module

public import SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence
public import SerrePositivity.InfinityCategories.Stable.StableVertexClosure

/-!
概要：完全関手の核として同定された本質像は、元の実頂点の安定閉包で変わらない。
方針：完全関手の安定閉包の零化と、核の両方向の同定を使う。
規約：包含の本質像をより大きい集合へ変更しない。使われ方：既存の実 cofiber 分母計算。
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

lemma stableClosure_eq_of_exact_kernel {A T B : StableCategory.{u}}
    (i : ExactMap A T) (F : ExactMap T B)
    (hk : ∀ x, IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) x) ↔ x ∈ essentialImage i) :
    {x | StableVertexClosure (essentialImage i) x} = essentialImage i := by
  ext x
  constructor
  · intro hx
    exact (hk x).mp (kills_stableVertexClosure F.hom (essentialImage i)
      (fun y hy => (hk y).mpr hy) hx)
  · exact StableVertexClosure.of_mem

lemma cofiberEdges_stableClosure_eq_of_exact_kernel {A T B : StableCategory.{u}}
    (i : ExactMap A T) (F : ExactMap T B)
    (hk : ∀ x, IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) x) ↔ x ∈ essentialImage i) :
    cofiberLocalizingEdges {x | StableVertexClosure (essentialImage i) x} =
      cofiberLocalizingEdges (essentialImage i) := by
  rw [stableClosure_eq_of_exact_kernel i F hk]

end SerrePositivity.KST.LocalizingInvariants
