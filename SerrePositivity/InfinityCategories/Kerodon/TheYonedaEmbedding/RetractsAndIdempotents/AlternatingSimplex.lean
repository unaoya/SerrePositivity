module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingAbsorption
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.TriangleKernel

/-!
概要：元の交互列 Y→X→Y→… の全射を持つ、元の強い分裂添字の実際の nerve 単体。
方針：偶奇で元の二対象を指定し、正の長さの全射を元の吸収射で構成する。
規約：元の二対象と元の包含・射影を保持し、単なる頂点列に置き換えない。
使われ方：HTT 4.4.5.6 の Ret(m) を貼る元の交互列の全単体。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の交互列の偶数位置は分裂対象、奇数位置は非分裂対象。 -/
def alternatingObject (i : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} :=
  if i % 2 = 1 then _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource else _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage

/-- 元の交互列の全ての射。長さ零だけを恒等とし、正の長さは元の吸収射。 -/
def alternatingChainMap {n : ℕ} (a b : Fin (n + 1)) :
    alternatingObject.{u} a.val ⟶ alternatingObject b.val :=
  if h : a = b then eqToHom (congrArg (fun i : Fin (n + 1) ↦ alternatingObject i.val) h)
  else _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom _ _

/-- 元の交互列の長さ零の射は、元の同じ対象の恒等。 -/
lemma alternatingChainMap_self {n : ℕ} (a : Fin (n + 1)) :
    alternatingChainMap.{u} a a = 𝟙 (alternatingObject a.val) := by
  simp [alternatingChainMap]

/-- 元の交互列の全射は元の順序の合成と整合する。 -/
lemma alternatingChainMap_comp {n : ℕ} (a b c : Fin (n + 1))
    (hab : a ≤ b) (hbc : b ≤ c) :
    alternatingChainMap.{u} a c = alternatingChainMap a b ≫ alternatingChainMap b c := by
  by_cases he : a = b
  · subst b
    simp [alternatingChainMap]
  by_cases hf : b = c
  · subst c
    simp [alternatingChainMap]
  have hg : a ≠ c := by
    intro h
    subst c
    exact he (le_antisymm hab hbc)
  simp only [alternatingChainMap, dite_eq_right he, dite_eq_right hf, dite_eq_right hg]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom _ _)).symm

/-- 元の交互列は、全ての元の射・恒等・合成を持つ実際の nerve 単体。 -/
def alternatingChain (n : ℕ) : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u} n where
  obj a := alternatingObject a.val
  map _f := alternatingChainMap _ _
  map_id a := alternatingChainMap_self a
  map_comp f g := alternatingChainMap_comp _ _ _ (leOfHom f) (leOfHom g)

/-- Ret(m) を貼る元の長さ 2m の交互列の全単体。 -/
def alternatingCell (m : ℕ) : (Δ[2 * m] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape :=
  SSet.yonedaEquiv.symm (alternatingChain (2 * m))

/-- 元の交互列の全単体での対象作用は、元の位置の偶奇そのもの。 -/
lemma alternatingCell_obj {m n : ℕ} (a : (Δ[2 * m] : SSet.{u}) _⦋n⦌)
    (i : Fin (n + 1)) :
    ((alternatingCell m).app (Opposite.op ⦋n⦌) a).obj i = alternatingObject (a i).val := rfl

/-- 元の交互列の非分裂対象の逆像は、元の奇数頂点の逆像そのもの。 -/
lemma alternatingCell_source_iff {m n : ℕ} (a : (Δ[2 * m] : SSet.{u}) _⦋n⦌)
    (i : Fin (n + 1)) :
    ((alternatingCell m).app (Opposite.op ⦋n⦌) a).obj i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource ↔
      (a i).val % 2 = 1 := by
  rw [alternatingCell_obj]
  simp [alternatingObject, Ne.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource_ne_image]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
