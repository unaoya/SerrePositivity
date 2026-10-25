module
public import SerrePositivity.InfinityCategories.Stable.CofiberLocalizingEdges
/-!
概要：完全関手の零対象核に cofiber を持つ辺は、同じ関手が反転する辺と一致する。
方針：実 cofiber 四角形の可逆性と零性の同値を両向きに使う。
規約：元の辺・実 cofiber を保持し、局所化や核の存在を仮定しない。
使われ方：D-16 の thick 核の辺集合を実商の反転飽和へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {X Y : SSet.{u}} [Quasicategory X] [IsStable X]
  [Quasicategory Y] [IsStable Y] (F : X ⟶ Y) [IsExactFunctor F]

lemma cofiberLocalizingEdges_zeroKernel_eq_invertedEdges :
    cofiberLocalizingEdges {x | IsZeroVertex (F.app (Opposite.op ⦋0⦌) x)} =
      invertedEdges F := by
  apply Set.Subset.antisymm
  · exact inverts_cofiberLocalizingEdges_of_kills F _ (fun _ h => h)
  · intro a ha
    let s := chosenCofiberSquare (edgeOfSimplex a)
    exact ⟨s, s.cofiber, (s.map_isInvertible_iff_zero F).1 ha, ⟨Iso.refl _⟩⟩

lemma cofiberLocalizingEdges_eq_invertedEdges_of_kernel
    (P : Set (X _⦋0⦌))
    (hP : ∀ x, IsZeroVertex (F.app (Opposite.op ⦋0⦌) x) ↔ x ∈ P) :
    cofiberLocalizingEdges P = invertedEdges F := by
  have h : P = {x | IsZeroVertex (F.app (Opposite.op ⦋0⦌) x)} :=
    Set.ext (fun x => (hP x).symm)
  rw [h]
  exact cofiberLocalizingEdges_zeroKernel_eq_invertedEdges F

end SerrePositivity.InfinityCategories
