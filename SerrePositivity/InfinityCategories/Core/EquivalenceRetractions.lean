module

public import SerrePositivity.InfinityCategories.Core.KanFibrationTools

/-!
概要：同値の二つの厳密な左逆の自然同型。
方針：選ばれた逆との同型を余単位から作って合成する。
規約：左逆の等式のみを要求する。
使われ方：Kerodon §4.6.4 の円柱の両端の比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：同値の二つの厳密な左逆は関手として同型。
方針：同値の逆合成の同型を二つの左逆で後合成する。
規約：始域・標的は quasicategory。
使われ方：Kerodon Lemma 4.6.4.25 の固定図式上の円柱の両端。 -/
lemma IsQCatEquivalence.nonempty_functorIso_of_retractions {E F : SSet.{u}}
    [Quasicategory E] [Quasicategory F] {e : E ⟶ F} (he : IsQCatEquivalence e)
    (s t : F ⟶ E) (hs : e ≫ s = 𝟙 E) (ht : e ≫ t = 𝟙 E) :
    Nonempty (FunctorIso s t) := by
  let a := he.choose
  have es := FunctorIso.postcomp a.invHomIso s
  have et := FunctorIso.postcomp a.invHomIso t
  change FunctorIso ((a.inv ≫ e) ≫ s) ((𝟙 F) ≫ s) at es
  change FunctorIso ((a.inv ≫ e) ≫ t) ((𝟙 F) ≫ t) at et
  rw [Category.assoc, hs, Category.comp_id, Category.id_comp] at es
  rw [Category.assoc, ht, Category.comp_id, Category.id_comp] at et
  exact ⟨es.symm ≪≫ et⟩

end SerrePositivity.InfinityCategories
