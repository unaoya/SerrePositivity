module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CubeSurjectionReduction

/-! # 単調全射の fiber max の connection のみによる実現
概要：任意の単調全射の fiber max を、隣接 connection だけの合成として実現する。
方針：厳密単調なら恒等、そうでなければ同じ値の隣接二入力を縮約し次元で帰納する。
規約：零次元も含み、面・削除を max 工程に混ぜない。使われ方：support ブロックの正規化。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction

/-- 元の具体的な関数が隣接 connection だけから生成される条件。 -/
inductive CubeConnectionGenerated : {n m : ℕ} → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) → Prop
  | id (n : ℕ) : CubeConnectionGenerated (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n)
  | connection (n : ℕ) (p : Fin (n + 1)) :
      CubeConnectionGenerated (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n p)
  | comp {n m k : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m} {g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex k}
      (hf : CubeConnectionGenerated f) (hg : CubeConnectionGenerated g) :
      CubeConnectionGenerated (g ∘ f)

/-- connection だけで生成された元の関数は、具体的な立方体圏の射。 -/
lemma cubeConnectionGenerated_generated {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeConnectionGenerated f) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated f := by
  induction h with
  | id n => exact .id n
  | connection n p => exact .connection n p
  | comp hf hg ihf ihg => exact .comp ihf ihg

/-- 元の単調全射の fiber max は、隣接 connection だけの合成で実現される。 -/
lemma cubeFiberMax_connectionGenerated {n m : ℕ} (q : Fin n → Fin m)
    (hq : Monotone q) (hs : Function.Surjective q) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeConnectionGenerated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax q) := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    by_cases ht : StrictMono q
    · have hm : m = n := by
        simpa only [Fintype.card_fin] using (Fintype.card_of_bijective ⟨ht.injective, hs⟩).symm
      subst m
      rw [ht.eq_id, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_id]
      exact .id n
    · cases n with
      | zero =>
        exact (ht (by intro i; exact Fin.elim0 i)).elim
      | succ n =>
        cases n with
        | zero =>
          apply False.elim
          apply ht
          intro i j hij
          have hi := i.isLt
          have hj := j.isLt
          change i.val < j.val at hij
          omega
        | succ n =>
          obtain ⟨p, hp⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeMonotone_exists_adjacent_eq q hq ht
          rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_lower q p hp]
          exact .comp (.connection n p)
            (ih (n + 1) (by omega) _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSurjectionLower_monotone q p hq)
              (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSurjectionLower_surjective q p hp hs))

/-- 元の単調全射の fiber max は、元の具体的な cubical 生成関数。 -/
lemma cubeFiberMax_generated {n m : ℕ} (q : Fin n → Fin m)
    (hq : Monotone q) (hs : Function.Surjective q) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax q) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeConnectionGenerated_generated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_connectionGenerated q hq hs)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
