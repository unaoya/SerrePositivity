module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.WeightedSectionCoefficients

/-!
概要：weighted nerve の切断の族を over 圏の射列で評価する。
方針：底を忘れた射列の最後の係数を取り、over の最後の構造射で後合成する。
規約：標準単体からの射として評価を定義し、面と退化の式を検証する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断から Bousfield–Kan 重みへの逆構成。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {I : Type u} [SmallCategory I] {A : SSet.{u}} {H : I ⥤ SSet.{u}}

/-- 概要：切断の族を over 圏の射列の終点で評価した標準単体。
方針：元の圏の射列上の最後の係数を、その構造射で指定の終点へ移す。
規約：パラメータと over 圏の射列は同じ次数。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の重み付き自然変換の各次数の成分。 -/
noncomputable def weightedSectionOverSimplex (s : nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A)
    {i : I} {n : ℕ} (σ : ComposableArrows (Over i) n) (a : A _⦋n⦌) :
    (Δ[n] : SSet.{u}) ⟶ H.obj i :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionCoefficients s hs (σ ⋙ Over.forget i) a).app (Fin.last n) ≫
    H.map (σ.obj (Fin.last n)).hom

/-- 概要：over 圏の射列の終点を後合成で移すと評価も同じ射で後合成される。
方針：元の射列が変わらないことと H の合成の保存を使う。
規約：元の圏の射は任意で、同型性は要求しない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の重みの添字に関する自然性。 -/
lemma weightedSectionOverSimplex_map (s : nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A)
    {i j : I} (f : i ⟶ j) {n : ℕ} (σ : ComposableArrows (Over i) n) (a : A _⦋n⦌) :
    weightedSectionOverSimplex s hs (σ ⋙ Over.map f) a =
      weightedSectionOverSimplex s hs σ a ≫ H.map f := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionCoefficients s hs (σ ⋙ Over.forget i) a).app (Fin.last n) ≫
    H.map ((σ.obj (Fin.last n)).hom ≫ f) = _
  rw [H.map_comp, ← Category.assoc]
  rfl

/-- 概要：over 圏の射列での評価は任意の単体作用素に沿う制限と可換。
方針：係数の制限公式、係数の初区間の自然性、over の三角形の可換性を組み合わせる。
規約：作用素は最後の頂点を保つ必要がない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の逆構成の単体的自然性。 -/
lemma weightedSectionOverSimplex_restriction (s : nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A)
    {i : I} {m n : SimplexCategory} (α : m ⟶ n)
    (σ : ComposableArrows (Over i) n.len) (a : A _⦋n.len⦌) :
    weightedSectionOverSimplex s hs ((SimplexCategory.toCat.map α).toFunctor ⋙ σ)
        (A.map α.op a) =
      stdSimplex.map α ≫ weightedSectionOverSimplex s hs σ a := by
  let k := α.toOrderHom (Fin.last m.len)
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionCoefficients s hs (σ ⋙ Over.forget i) a
  have hc := NatTrans.congr_app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionCoefficients_restriction s hs α (σ ⋙ Over.forget i) a) (Fin.last m.len)
  have ht := τ.naturality (homOfLE (Fin.le_last k))
  change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion k.val n.len (Fin.le_last k)) ≫
    τ.app (Fin.last n.len) = τ.app k ≫ H.map (σ.map (homOfLE (Fin.le_last k))).left at ht
  have hα : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α (Fin.last m.len) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion k.val n.len (Fin.le_last k) = α := by
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_factor α (Fin.last m.len)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion m.len m.len le_rfl ≫ α =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α (Fin.last m.len) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion k.val n.len (Fin.le_last k) at he
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_id, Category.id_comp] at he
    exact he.symm
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionCoefficients s hs
      ((SimplexCategory.toCat.map α).toFunctor ⋙ (σ ⋙ Over.forget i))
        (A.map α.op a)).app (Fin.last m.len) ≫ H.map (σ.obj k).hom =
      stdSimplex.map α ≫ (τ.app (Fin.last n.len) ≫ H.map (σ.obj (Fin.last n.len)).hom)
  rw [hc]
  change (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α (Fin.last m.len)) ≫ τ.app k) ≫
    H.map (σ.obj k).hom = _
  rw [← Over.w (σ.map (homOfLE (Fin.le_last k))), H.map_comp, Category.assoc,
    ← Category.assoc (τ.app k), ← ht]
  simp only [← Category.assoc]
  rw [← Functor.map_comp, hα]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
