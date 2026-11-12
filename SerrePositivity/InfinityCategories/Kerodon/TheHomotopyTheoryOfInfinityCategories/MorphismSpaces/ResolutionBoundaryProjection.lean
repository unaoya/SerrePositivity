module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionFiniteGluing

/-!
概要：明示的な旗の境界上で解像の射影は前合成による同値を与える。
方針：全ての一頂点を除く面の有限族を使い、面の和の同値性を境界へ移す。
規約：一般の左 Kan 拡張を境界に適用したものとの同定は別途必要。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界から標準単体への相対比較の入力。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：標準単体の境界を覆う余次元一の面の頂点集合の族。
方針：各頂点を一つ除いた補集合を有限集合の image として取る。
規約：零単体では空の面だけからなる族。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界を有限の面の和として扱う。 -/
def coherentResolutionBoundaryFaces (n : ℕ) : Finset (Finset (Fin (n + 1))) :=
  Finset.univ.image (fun j ↦ ({j} : Finset (Fin (n + 1)))ᶜ)

/-- 概要：余次元一の面族の解像の和は明示的な境界。
方針：台が真部分集合であることを、含まれない頂点の存在で表す。
規約：次数零を含む全ての標準単体で成立する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、有限の面の和から境界への移送。 -/
lemma coherentResolutionFaceUnion_boundaryFaces (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion.{u} (coherentResolutionBoundaryFaces n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionBoundary n := by
  classical
  apply Subfunctor.ext
  funext d
  apply Set.ext
  intro F
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mem_coherentResolutionFaceUnion_iff (coherentResolutionBoundaryFaces n) F).trans ?_
  change (∃ T ∈ coherentResolutionBoundaryFaces n, F.down.support ⊆ T) ↔
    F.down.support ≠ Finset.univ
  constructor
  · rintro ⟨T, hT, hF⟩ hfull
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hT
    have hj := hF (hfull.symm ▸ Finset.mem_univ j)
    exact (Finset.mem_compl.mp hj) (Finset.mem_singleton_self j)
  · intro hF
    have hx : ∃ j, j ∉ F.down.support := by
      by_contra hn
      apply hF
      apply Finset.eq_univ_iff_forall.mpr
      intro j
      by_contra hj
      exact hn ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hx
    refine ⟨{j}ᶜ, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    intro k hk
    apply Finset.mem_compl.mpr
    intro heq
    have hkj : k = j := Finset.mem_singleton.mp heq
    exact hj (hkj ▸ hk)

/-- 概要：同じ面族の標準単体の面の和は通常の境界。
方針：有限和を全頂点にわたる上限に展開し、境界の既存の表示を使う。
規約：通常の単体集合の境界 ∂Δ[n] と同一視する。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界の射影の標的の同定。 -/
lemma stdSimplexFaceUnion_boundaryFaces (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion.{u} (coherentResolutionBoundaryFaces n) = SSet.boundary n := by
  classical
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion coherentResolutionBoundaryFaces
  rw [Finset.sup_image, Finset.sup_eq_iSup]
  simp only [Finset.mem_univ, iSup_pos, Function.comp_apply]
  exact (SSet.boundary_eq_iSup n).symm

/-- 概要：明示的な解像の境界は射影で標準単体の境界へ写る。
方針：境界を面の有限和として表し、和に対する所属条件を使う。
規約：解像の境界に関する制限条件。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界上の射影の定義。 -/
lemma coherentResolutionBoundary_mapsTo (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionBoundary.{u} n ≤ (SSet.boundary n).preimage
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n) := by
  rw [← coherentResolutionFaceUnion_boundaryFaces, ← stdSimplexFaceUnion_boundaryFaces]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_mapsTo _

/-- 概要：明示的な旗の境界から標準単体の境界への射影。
方針：最大元の射影を二つの境界へ制限する。
規約：左 Kan 拡張に対する境界の射影とはまだ同定しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標準単体への相対比較。 -/
def coherentResolutionBoundaryProjection (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionBoundary.{u} n).toSSet ⟶ (SSet.boundary n).toSSet :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.subcomplexRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n) _ _ (coherentResolutionBoundary_mapsTo n)

/-- 概要：境界上の射影は大きい単体の射影の制限。
方針：部分複体の制限射と包含の可換式を使う。
規約：境界の包含を後に合成した式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界と標準単体の射影の可換図式。 -/
lemma coherentResolutionBoundaryProjection_ι (n : ℕ) :
    coherentResolutionBoundaryProjection.{u} n ≫ (SSet.boundary n).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionBoundary n).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n := rfl

/-- 概要：明示的な境界上の解像の射影は前合成による同値。
方針：有限個の面の和上の同値性を、両側の境界の同定で移す。
規約：零単体の空の境界も含む。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界からの相対拡張の比較。 -/
lemma coherentResolutionBoundaryProjection_isPrecompositionEquivalence (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (coherentResolutionBoundaryProjection.{u} n) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.subcomplexRestriction_isPrecompositionEquivalence_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_mapsTo (coherentResolutionBoundaryFaces n))
    (coherentResolutionBoundary_mapsTo n) (coherentResolutionFaceUnion_boundaryFaces n)
    (stdSimplexFaceUnion_boundaryFaces n)).mp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnionProjection_isPrecompositionEquivalence _)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
