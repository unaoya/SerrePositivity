module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionSupport

/-!
概要：標準単体の旗の解像の中で境界に対応する部分複体。
方針：台が全頂点集合と異なる旗を取り、各面の解像の像の和として表す。
規約：一般の左 Kan 拡張を境界に適用したものとの同定は別途示す。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界を使う解像の貼り合わせ。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：全ての頂点を使わない旗からなる解像の部分複体。
方針：引き戻しでは台が増えないことを使う。
規約：境界の明示的な模型であり、左 Kan 拡張との同定は後で行う。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標準単体の境界上の解像。 -/
def coherentResolutionBoundary (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n).Subcomplex where
  obj _ := {F | F.down.support ≠ Finset.univ}
  map {a b} α F hF hnew := by
    change (F.down.pullback α.unop.toOrderHom).support = Finset.univ at hnew
    apply hF
    apply Finset.eq_univ_iff_forall.mpr
    intro k
    apply F.down.support_pullback_subset α.unop.toOrderHom
    rw [hnew]
    exact Finset.mem_univ _

/-- 概要：零単体の解像の境界は空。
方針：頂点は一つしかなく、旗はその始点を台に含む。
規約：次数零の基底例。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界による帰納法の初期条件。 -/
lemma coherentResolutionBoundary_zero : coherentResolutionBoundary.{u} 0 = ⊥ := by
  apply le_antisymm _ bot_le
  intro d F hF
  apply hF
  apply Finset.eq_univ_iff_forall.mpr
  intro k
  have hk : k = F.down.start := (Fin.eq_zero k).trans (Fin.eq_zero F.down.start).symm
  rw [hk]
  exact F.down.start_mem _

/-- 概要：ある面の解像の直接像に入る旗は、その面の除く頂点を台に含まない旗。
方針：単射な直接像の像の判定と succAbove の像を使う。
規約：頂点 j を除く面 Δ[n] から Δ[n+1] を扱う。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界の解像の面ごとの表示。 -/
lemma CoherentResolutionFlag.mem_range_face_iff {n d : ℕ}
    (j : Fin (n + 2)) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag (n + 1) d) :
    F ∈ Set.range (fun G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d ↦
      G.pushforward (SimplexCategory.δ j).toOrderHom) ↔ j ∉ F.support := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.mem_range_pushforward_iff _ (Fin.succAboveOrderEmb j).injective]
  change (∀ k ∈ F.support, k ∈ Set.range j.succAbove) ↔ _
  rw [Fin.range_succAbove]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · intro h hj
    exact h j hj rfl
  · intro hj k hk heq
    exact hj (heq ▸ hk)

/-- 概要：面の解像の射の range 部分複体を台の条件で計算する。
方針：ULift を戻して有限集合の旗の像の特徴づけを使う。
規約：任意の次数の単体に適用する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界の面の像の和による記述。 -/
lemma mem_range_coherentResolutionFace_iff {n d : ℕ} (j : Fin (n + 2))
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} (n + 1)) _⦋d⦌) :
    F ∈ (Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap (SimplexCategory.δ j).toOrderHom)).obj
      (Opposite.op ⦋d⦌) ↔ j ∉ F.down.support := by
  change (∃ G : ULift.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d),
    ULift.up (G.down.pushforward (SimplexCategory.δ j).toOrderHom) = F) ↔ _
  constructor
  · rintro ⟨G, hG⟩
    exact (F.down.mem_range_face_iff j).mp ⟨G.down, congrArg ULift.down hG⟩
  · intro hF
    obtain ⟨G, hG⟩ := (F.down.mem_range_face_iff j).mpr hF
    exact ⟨ULift.up G, ULift.ext hG⟩

/-- 概要：正次数の解像の境界は各面の解像の像の和。
方針：台が全頂点集合でないことは、台に含まれない頂点の存在と同値。
規約：和は単体集合の部分複体の上限。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、有限個の面から境界を貼り合わせる記述。 -/
lemma coherentResolutionBoundary_eq_iSup_faces (n : ℕ) :
    coherentResolutionBoundary.{u} (n + 1) =
      ⨆ j : Fin (n + 2),
        Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap (SimplexCategory.δ j).toOrderHom) := by
  classical
  apply Subfunctor.ext
  funext d
  obtain ⟨⟨d⟩⟩ := d
  apply Set.ext
  intro F
  change F.down.support ≠ Finset.univ ↔ _
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · intro h
    have hx : ∃ j, j ∉ F.down.support := by
      by_contra hn
      apply h
      apply Finset.eq_univ_iff_forall.mpr
      intro j
      by_contra hj
      exact hn ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, (mem_range_coherentResolutionFace_iff j F).mpr hj⟩
  · rintro ⟨j, hj⟩ hfull
    have hnot := (mem_range_coherentResolutionFace_iff j F).mp hj
    exact hnot (hfull.symm ▸ Finset.mem_univ j)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
