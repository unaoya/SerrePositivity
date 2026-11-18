module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorSelectionCard

/-!
概要：選択集合上で単射な任意作用素の像の列挙は、同じ選択列と元の作用素の合成である。
方針：昇順列挙との合成を全域単射な単調写像とし、元の列挙の一意性を使う。
規約：作用素全体の単射性は仮定しない。使われ方：全再添字の非退化分岐。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open scoped _root_.Simplicial

lemma normalizedTensorElementSelectionOfCard_image_of_injOn {m n r : ℕ}
    (J : Finset (Fin (m + 1))) (θ : ⦋m⦌ ⟶ ⦋n⦌) (hc : J.card = r + 1)
    (hi : Set.InjOn θ.toOrderHom (J : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectionOfCard (J.image θ.toOrderHom) r
      (by rw [Finset.card_image_of_injOn hi]; exact hc) =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectionOfCard J r hc ≫ θ := by
  have hφ : Function.Injective (fun i : Fin (r + 1) => θ.toOrderHom (J.orderEmbOfFin hc i)) := by
    intro i j hij
    exact (J.orderEmbOfFin hc).injective
      (hi (J.orderEmbOfFin_mem hc i) (J.orderEmbOfFin_mem hc j) hij)
  have hu : (fun i : Fin (r + 1) => θ.toOrderHom (J.orderEmbOfFin hc i)) =
      (J.image θ.toOrderHom).orderEmbOfFin
        (by rw [Finset.card_image_of_injOn hi]; exact hc) :=
    Finset.orderEmbOfFin_unique _
      (fun i => Finset.mem_image.mpr ⟨_, J.orderEmbOfFin_mem hc i, rfl⟩)
      ((θ.toOrderHom.monotone.comp (J.orderEmbOfFin hc).monotone).strictMono_of_injective hφ)
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  exact (congrFun hu i).symm

end SerrePositivity.ComplexLimits
