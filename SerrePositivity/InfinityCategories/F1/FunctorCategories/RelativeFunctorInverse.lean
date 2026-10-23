module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostLaws
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverEquivalence

/-!
概要：同じ底上の left fibrations の前合成同値から相対的な逆射を得る。
方針：相対前合成の本質的全射性で逆射と片側の単位を選び、充満忠実性で他方を戻す。
規約：両側の比較は底を固定した相対関手空間内に保持する。
使われ方：Kerodon Corollary 5.6.0.6、相対写像空間の後合成による同値不変性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の left fibrations の前合成同値は、底上の逆射と相対的な単位・余単位を持つ。
方針：恒等相対関手を前合成同値で戻し、相対後合成と充満忠実性で他方の逆条件を証明する。
規約：底 B は quasicategory。二つの同型は底上の相対関手空間内で取る。
使われ方：Kerodon Corollary 5.6.0.6、同じ底上の同値の相対的な逆データ。 -/
lemma exists_relativeFunctorInverse_of_precompositionEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    ∃ (g : F ⟶ E) (hg : g ≫ p = q),
      Nonempty (VertexIso
        (relativeFunctorVertex p p (f ≫ g) (by rw [Category.assoc, hg, hf]))
        (relativeFunctorVertex p p (𝟙 E) (Category.id_comp p))) ∧
      Nonempty (VertexIso
        (relativeFunctorVertex q q (g ≫ f) (by rw [Category.assoc, hf, hg]))
        (relativeFunctorVertex q q (𝟙 F) (Category.id_comp q))) := by
  let f' : Over.mk p ⟶ Over.mk q := Over.homMk f hf
  have he := relativeFunctorOverPre_isQCatEquivalence p f' ef
  obtain ⟨v, ⟨hv⟩⟩ := he.choose.isEssentiallySurjective
    (relativeFunctorVertex p p (𝟙 E) (Category.id_comp p))
  obtain ⟨g, hg, hvg⟩ := exists_relativeFunctorVertex p q v
  have hunit : VertexIso
      (relativeFunctorVertex p p (f ≫ g) (by rw [Category.assoc, hg, hf]))
      (relativeFunctorVertex p p (𝟙 E) (Category.id_comp p)) := by
    rw [← hvg] at hv
    exact hv
  have hcomp : VertexIso
      ((relativeFunctorOverPre q f').app _ (relativeFunctorVertex q q (g ≫ f)
        (by rw [Category.assoc, hf, hg])))
      ((relativeFunctorOverPre q f').app _ (relativeFunctorVertex q q (𝟙 F) (Category.id_comp q))) := by
    change VertexIso (relativeFunctorVertex q p (f ≫ (g ≫ f))
      (by simp only [Category.assoc, hf, hg]))
      (relativeFunctorVertex q p (f ≫ 𝟙 F) (by rw [Category.comp_id, hf]))
    simpa only [relativeFunctorPost_vertex,
      Category.assoc, Category.id_comp, Category.comp_id] using
      VertexIso.map hunit (HomotopyLimits.relativeFunctorPost p q f hf p)
  have hcounit := (relativeFunctorOverPre_isQCatEquivalence q f' ef).isFullyFaithful.preimageVertexIso
    hcomp
  exact ⟨g, hg, ⟨hunit⟩, ⟨hcounit⟩⟩

end SerrePositivity.InfinityCategories
