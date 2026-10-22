module

public import SerrePositivity.InfinityCategories.F2.CoherentPositiveInterval
public import SerrePositivity.InfinityCategories.F2.CoherentPrefixConeSimplex

/-!
概要：固定始点の prefix 変形の tail は元の tail だけの prefix 変形。
方針：正頂点包含の区間の全射性と添字変換を使う。
規約：全ての tail 単体と時刻を保持する。
使われ方：標準図式を固定する全 coslice 円柱の射影。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 固定始点の prefix 単体の tail は元の tail の同じ変形に厳密に等しい。 -/
lemma coherentPrefixConeSimplex_tail {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {m n : ℕ} (s : (SimplicialNerve C) _⦋n + 1⦌)
    (a : Fin (m + 1) →o Fin (n + 1)) (t : Fin (m + 1) →o Fin 2) :
    (SimplicialNerve C).δ 0 (coherentPrefixConeSimplex s a t) =
      (coherentPrefixPathDeformationEnriched a.uliftMap
        (t.comp (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin (m + 1)) →o _))).comp
          SSet ((SimplicialNerve C).δ 0 s) := by
  change ((SimplicialThickening.functor
    (SimplexCategory.δ (0 : Fin (m + 2))).toOrderHom.uliftMap).comp SSet
      (coherentPrefixPathDeformationEnriched _ _)).comp SSet s = _
  rw [coherentPrefixPathDeformationEnriched_reindex]
  have ha : (prependOrderHom a).uliftMap.comp
      (SimplexCategory.δ (0 : Fin (m + 2))).toOrderHom.uliftMap =
      (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom.uliftMap.comp
        a.uliftMap := by
    ext i
    rcases i with ⟨i⟩
    rfl
  have ht : ((coherentPrefixConeTime t).comp
      (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin (m + 2)) →o _)).comp
      (SimplexCategory.δ (0 : Fin (m + 2))).toOrderHom.uliftMap =
      t.comp (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin (m + 1)) →o _) := by
    ext i
    rcases i with ⟨i⟩
    rfl
  rw [ha, ht, coherentPrefixPathDeformationEnriched_target_map _ _ _
    (coherentPositiveVertex_interval n)]
  rfl

end SerrePositivity.InfinityCategories.F2
