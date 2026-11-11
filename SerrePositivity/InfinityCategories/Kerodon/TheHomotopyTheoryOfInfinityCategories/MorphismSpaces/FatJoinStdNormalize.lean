module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinStdClamp
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTransform
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinVertices

/-!
概要：標準単体の fat join の左右の成分の正規化。
方針：単調写像を標準単体の射にし、端点を保つ円柱変換として貼り合わせる。
規約：この段階では正規化へのホモトピーはまだ構成しない。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の標準単体の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：左の正規化の単体集合の射は零端を固定する。
方針：各頂点で有限順序集合の零端の計算を使う。
規約：任意の標準 n 単体。
使われ方：Kerodon §4.6.2（Tag 01HM） の左因子の固定。 -/
lemma stdSimplexProductMap_leftClamp_zero (n : ℕ) :
    SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp n) = 𝟙 (Δ[n] : SSet.{u}) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp_zero n (a i)

/-- 概要：右の正規化の単体集合の射は一端を固定する。
方針：各頂点で有限順序集合の一端の計算を使う。
規約：任意の標準 n 単体。
使われ方：Kerodon §4.6.2（Tag 01HM） の右因子の固定。 -/
lemma stdSimplexProductMap_rightClamp_one (n : ℕ) :
    SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClamp n) = 𝟙 (Δ[n] : SSet.{u}) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClamp_one n (a i)

/-- 概要：標準単体の fat join の左成分を正規化する自己射。
方針：一端で左成分を最後の頂点に移し、右成分は保つ。
規約：左右の包含上は恒等。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の変形の終点。 -/
noncomputable def fatJoinStdLeftNormalize (n m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTransform (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp n)) (fst Δ[m] Δ[1])
    (stdSimplexProductMap_leftClamp_zero n) (by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro a
      rfl)

/-- 概要：標準単体の fat join の左右の成分を正規化する自己射。
方針：左成分を一端で最後の頂点、右成分を零端で零へ移す。
規約：左右の包含上は恒等。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の変形の始点。 -/
noncomputable def fatJoinStdNormalize (n m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTransform (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp n))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClamp m))
    (stdSimplexProductMap_leftClamp_zero n) (stdSimplexProductMap_rightClamp_one m)

/-- 概要：左の正規化は全ての頂点を固定する。
方針：fat join の頂点は左右の包含に由来し、その包含を正規化が固定する。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の変形の頂点の固定。 -/
lemma fatJoinStdLeftNormalize_vertex (n m : ℕ) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m]) _⦋0⦌) :
    (fatJoinStdLeftNormalize n m).app (Opposite.op ⦋0⦌) x = x := by
  obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_vertex_cases Δ[n] Δ[m] x
  · exact congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin Δ[n] Δ[m] ↦
      f.app (Opposite.op ⦋0⦌) a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_transform _ _ _ _)
  · exact congrArg (fun f : (Δ[m] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin Δ[n] Δ[m] ↦
      f.app (Opposite.op ⦋0⦌) b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_transform _ _ _ _)

/-- 概要：左右の正規化も全ての頂点を固定する。
方針：左右の包含の像に分け、その固定の計算を使う。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の変形の頂点の固定。 -/
lemma fatJoinStdNormalize_vertex (n m : ℕ) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m]) _⦋0⦌) :
    (fatJoinStdNormalize n m).app (Opposite.op ⦋0⦌) x = x := by
  obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_vertex_cases Δ[n] Δ[m] x
  · exact congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin Δ[n] Δ[m] ↦
      f.app (Opposite.op ⦋0⦌) a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_transform _ _ _ _)
  · exact congrArg (fun f : (Δ[m] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin Δ[n] Δ[m] ↦
      f.app (Opposite.op ⦋0⦌) b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_transform _ _ _ _)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
