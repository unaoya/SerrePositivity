module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementSelectedCochain

/-!
概要：同じ明示次数の選択列を定義し、順序埋め込みによる像の選択列と合成を比較する。
方針：昇順列挙の一意性で元の二つの埋め込みを一致させる。
規約：同じ有限集合・列挙・次数を保つ。使われ方：選択 cochain の単射再添字。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open scoped _root_.Simplicial

abbrev normalizedTensorElementSelectionOfCard {n : ℕ} (J : Finset (Fin (n + 1)))
    (r : ℕ) (hc : J.card = r + 1) : ⦋r⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom

lemma normalizedTensorElementSelectionOfCard_last {n : ℕ} (J : Finset (Fin (n + 1)))
    (r : ℕ) (hc : J.card = r + 1) (hJ : J.Nonempty) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectionOfCard J r hc).toOrderHom (Fin.last r) = J.max' hJ :=
  Finset.orderEmbOfFin_last hc (by omega)

lemma normalizedTensorElementSelectionOfCard_image {m n r : ℕ}
    (J : Finset (Fin (m + 1))) (e : Fin (m + 1) ↪o Fin (n + 1)) (hc : J.card = r + 1) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectionOfCard (J.image e) r
      (by rw [Finset.card_image_of_injective _ e.injective]; exact hc) =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectionOfCard J r hc ≫ SimplexCategory.mkHom e.toOrderHom := by
  have he : (J.image e).orderEmbOfFin
      (show (J.image e).card = r + 1 by
        rw [Finset.card_image_of_injective _ e.injective]; exact hc) =
      (J.orderEmbOfFin hc).trans e := by
    apply DFunLike.ext
    intro i
    have hu : (fun i : Fin (r + 1) => e (J.orderEmbOfFin hc i)) =
        (J.image e).orderEmbOfFin
          (by rw [Finset.card_image_of_injective _ e.injective]; exact hc) :=
      Finset.orderEmbOfFin_unique _
        (fun i => Finset.mem_image.mpr ⟨_, J.orderEmbOfFin_mem hc i, rfl⟩)
        (e.strictMono.comp (J.orderEmbOfFin hc).strictMono)
    exact (congrFun hu i).symm
  apply SimplexCategory.Hom.ext
  exact congrArg (fun f : Fin (r + 1) ↪o Fin (n + 1) => f.toOrderHom) he

end SerrePositivity.ComplexLimits
