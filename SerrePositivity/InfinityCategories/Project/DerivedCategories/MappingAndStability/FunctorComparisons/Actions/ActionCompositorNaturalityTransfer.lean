module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.Actions.ActionPentagonTransfer
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange
/-!
概要：同じ指定比較と合成子の自然性を、全関手同型の等式として輸送する。
方針：実交換則・指定正方形・同じ末尾比較の消去を使う。
規約：新しい比較を選ばない。使われ方：元の導来 kernel 合成子 κ の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
noncomputable section
/-- 指定比較の正方形と自然性は、同じ元の合成子の自然性へ移る。 -/
lemma compositionComparison_transfer_naturality {X A Y B : SSet.{u}}
    (L : X ⟶ A) (M : Y ⟶ B) (S₀ S₁ T₀ T₁ : A ⟶ B) (G₀ G₁ U₀ U₁ : X ⟶ Y)
    (x₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ T₀) (U₀ ≫ M)) (x₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ T₁) (U₁ ≫ M))
    (n₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ S₀) (G₀ ≫ M)) (n₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ S₁) (G₁ ≫ M))
    (c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso S₀ T₀) (c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso S₁ T₁)
    (i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso S₀ S₁) (j : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G₀ G₁)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso T₀ T₁) (u : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso U₀ U₁)
    (a₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G₀ U₀) (a₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G₁ U₁)
    (hc₀ : c₀.precomp L ≪≫ x₀ = n₀ ≪≫ a₀.postcomp M)
    (hc₁ : c₁.precomp L ≪≫ x₁ = n₁ ≪≫ a₁.postcomp M)
    (hn : n₀ ≪≫ j.postcomp M = i.precomp L ≪≫ n₁)
    (hx : x₀ ≪≫ u.postcomp M = t.precomp L ≪≫ x₁)
    (ha : a₀ ≪≫ u = j ≪≫ a₁) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (c₀ ≪≫ t) L = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (i ≪≫ c₁) L := by
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (c₀ ≪≫ t) L ≪≫ x₁ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (i ≪≫ c₁) L ≪≫ x₁ := by
    calc
      _ = c₀.precomp L ≪≫ (t.precomp L ≪≫ x₁) := by
        rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, Iso.trans_assoc]
      _ = c₀.precomp L ≪≫ (x₀ ≪≫ u.postcomp M) := by rw [← hx]
      _ = (n₀ ≪≫ a₀.postcomp M) ≪≫ u.postcomp M := by
        rw [← Iso.trans_assoc, hc₀]
      _ = n₀ ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (a₀ ≪≫ u) M := by
        rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, Iso.trans_assoc]
      _ = n₀ ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (j ≪≫ a₁) M := by rw [ha]
      _ = (i.precomp L ≪≫ n₁) ≪≫ a₁.postcomp M := by
        rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, ← Iso.trans_assoc, hn]
      _ = i.precomp L ≪≫ (c₁.precomp L ≪≫ x₁) := by
        rw [Iso.trans_assoc, ← hc₁]
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, Iso.trans_assoc]
  apply Iso.ext
  exact (cancel_mono x₁.hom).mp (congrArg Iso.hom hh)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
