module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverEquivalence
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorExtensionEndpoint

/-!
概要：前合成同値に沿い left fibration への相対射を同型まで延長する。
方針：相対関手空間の制限の本質的全射性を実際の射に戻す。
規約：底の図式は厳密に保持し比較する同型も相対関手空間内に置く。
使われ方：写像円柱の pointed な図式を collage へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：前合成同値に沿う相対射の延長は相対写像空間の同型まで存在する。
方針：比較の本質的全射性と頂点の実際の射への全単射を使う。
規約：比較射の単射性や始域の quasicategory 性は要求しない。
使われ方：collage の図式を既存の coherent な変換から回収する。 -/
lemma exists_relativeFunctorExtension_of_precompositionEquivalence
    {A D E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (b : A ⟶ B) (i : D ⟶ A) (hi : IsPrecompositionEquivalence i)
    (W : D ⟶ E) (hW : W ≫ p = i ≫ b) :
    ∃ (L : A ⟶ E) (hL : L ≫ p = b),
      Nonempty (VertexIso
        (relativeFunctorVertex p (i ≫ b) (i ≫ L) (by rw [Category.assoc, hL]))
        (relativeFunctorVertex p (i ≫ b) W hW)) := by
  have he := relativeFunctorPre_isQCatEquivalence_of_precompositionEquivalence p b i hi
  obtain ⟨v, ⟨e⟩⟩ := he.choose.isEssentiallySurjective (relativeFunctorVertex p (i ≫ b) W hW)
  obtain ⟨L, hL, hv⟩ := exists_relativeFunctorVertex p b v
  rw [← hv] at e
  change VertexIso ((relativeFunctorPre p b i).app _ (relativeFunctorVertex p b L hL))
    (relativeFunctorVertex p (i ≫ b) W hW) at e
  rw [relativeFunctorPre_vertex] at e
  exact ⟨L, hL, ⟨e⟩⟩

end SerrePositivity.InfinityCategories
