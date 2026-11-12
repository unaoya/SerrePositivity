module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

/-!
概要：有限順序集合の直積の単調写像による標準単体の直積からの射。
方針：単体の各頂点に単調写像を作用させる。
規約：直積は二因子または三因子で、後者は左結合。
使われ方：Kerodon §4.6.2（Tag 01HM） の標準単体の fat join の変形。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：有限順序集合の直積の単調写像を標準単体の直積の射にする。
方針：各頂点の二つの値に単調写像を適用する。
規約：任意の自然数の三つの次数。
使われ方：Kerodon §4.6.2（Tag 01HM） の円柱の変形。 -/
def stdSimplexProductMap {a b c : ℕ} (f : Fin (a + 1) × Fin (b + 1) →o Fin (c + 1)) :
    (Δ[a] : SSet.{u}) ⊗ Δ[b] ⟶ Δ[c] where
  app n := by
    obtain ⟨⟨n⟩⟩ := n
    exact ↾fun s ↦ stdSimplex.objEquiv.symm (SimplexCategory.mkHom
      { toFun i := f (s.1 i, s.2 i)
        monotone' _ _ h := f.monotone
          ⟨stdSimplex.monotone_apply s.1 h, stdSimplex.monotone_apply s.2 h⟩ })
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply stdSimplex.ext
    intro i
    rfl

/-- 概要：単調写像から作った単体集合の射の頂点ごとの値。
方針：標準単体の順序写像の表示を展開する。
規約：i は入力単体の頂点の番号。
使われ方：Kerodon §4.6.2（Tag 01HM） の端点と自然性の計算。 -/
lemma stdSimplexProductMap_apply {a b c n : ℕ}
    (f : Fin (a + 1) × Fin (b + 1) →o Fin (c + 1))
    (s : ((Δ[a] : SSet.{u}) ⊗ Δ[b]) _⦋n⦌) (i : Fin (n + 1)) :
    (stdSimplexProductMap f).app (Opposite.op ⦋n⦌) s i = f (s.1 i, s.2 i) := rfl

/-- 概要：三つの有限順序集合の直積の単調写像を単体集合の射にする。
方針：各頂点の三つの値を同時に読む。
規約：直積は (Δ[a]×Δ[b])×Δ[c] の順。
使われ方：Kerodon §4.6.2（Tag 01HM） の変形の時間パラメーター。 -/
def stdSimplexTripleProductMap {a b c d : ℕ}
    (f : (Fin (a + 1) × Fin (b + 1)) × Fin (c + 1) →o Fin (d + 1)) :
    ((Δ[a] : SSet.{u}) ⊗ Δ[b]) ⊗ Δ[c] ⟶ Δ[d] where
  app n := by
    obtain ⟨⟨n⟩⟩ := n
    exact ↾fun s ↦ stdSimplex.objEquiv.symm (SimplexCategory.mkHom
      { toFun i := f ((s.1.1 i, s.1.2 i), s.2 i)
        monotone' _ _ h := f.monotone
          ⟨⟨stdSimplex.monotone_apply s.1.1 h, stdSimplex.monotone_apply s.1.2 h⟩,
            stdSimplex.monotone_apply s.2 h⟩ })
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply stdSimplex.ext
    intro i
    rfl

/-- 概要：三因子の単調写像から作った射の頂点ごとの値。
方針：定義の順序写像を展開する。
規約：三因子は左結合の順。
使われ方：Kerodon §4.6.2（Tag 01HM） の変形の計算。 -/
lemma stdSimplexTripleProductMap_apply {a b c d n : ℕ}
    (f : (Fin (a + 1) × Fin (b + 1)) × Fin (c + 1) →o Fin (d + 1))
    (s : (((Δ[a] : SSet.{u}) ⊗ Δ[b]) ⊗ Δ[c]) _⦋n⦌) (i : Fin (n + 1)) :
    (stdSimplexTripleProductMap f).app (Opposite.op ⦋n⦌) s i =
      f ((s.1.1 i, s.1.2 i), s.2 i) := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
