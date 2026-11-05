module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kan.CubeSurjectionReduction

/-! # 単調全射の fiber max の connection のみによる実現
概要：任意の単調全射の fiber max を、隣接 connection だけの合成として実現する。
方針：厳密単調なら恒等、そうでなければ同じ値の隣接二入力を縮約し次元で帰納する。
規約：零次元も含み、面・削除を max 工程に混ぜない。使われ方：support ブロックの正規化。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.SConstruction

/-- 元の具体的な関数が隣接 connection だけから生成される条件。 -/
inductive CubeConnectionGenerated : {n m : ℕ} → (_root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex m) → Prop
  | id (n : ℕ) : CubeConnectionGenerated (_root_.id : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n)
  | connection (n : ℕ) (p : Fin (n + 1)) :
      CubeConnectionGenerated (_root_.SerrePositivity.InfinityCategories.Simplicial.cubeVertexConnection n p)
  | comp {n m k : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex m} {g : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex k}
      (hf : CubeConnectionGenerated f) (hg : CubeConnectionGenerated g) :
      CubeConnectionGenerated (g ∘ f)

/-- connection だけで生成された元の関数は、具体的な立方体圏の射。 -/
lemma cubeConnectionGenerated_generated {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Simplicial.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated f) : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated f := by
  induction h with
  | _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.id n => exact .id n
  | _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.connection n p => exact .connection n p
  | _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.comp hf hg ihf ihg => exact .comp ihf ihg

/-- 元の単調全射の fiber max は、隣接 connection だけの合成で実現される。 -/
lemma cubeFiberMax_connectionGenerated {n m : ℕ} (q : Fin n → Fin m)
    (hq : Monotone q) (hs : Function.Surjective q) :
    _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated (_root_.SerrePositivity.InfinityCategories.Kan.cubeFiberMax q) := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    by_cases ht : StrictMono q
    · have hm : m = n := by
        simpa only [Fintype.card_fin] using (Fintype.card_of_bijective ⟨ht.injective, hs⟩).symm
      subst m
      rw [ht.eq_id, _root_.SerrePositivity.InfinityCategories.Kan.cubeFiberMax_id]
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
          obtain ⟨p, hp⟩ := _root_.SerrePositivity.InfinityCategories.Kan.cubeMonotone_exists_adjacent_eq q hq ht
          rw [_root_.SerrePositivity.InfinityCategories.Kan.cubeFiberMax_lower q p hp]
          exact .comp (.connection n p)
            (ih (n + 1) (by omega) _ (_root_.SerrePositivity.InfinityCategories.Kan.cubeSurjectionLower_monotone q p hq)
              (_root_.SerrePositivity.InfinityCategories.Kan.cubeSurjectionLower_surjective q p hp hs))

/-- 元の単調全射の fiber max は、元の具体的な cubical 生成関数。 -/
lemma cubeFiberMax_generated {n m : ℕ} (q : Fin n → Fin m)
    (hq : Monotone q) (hs : Function.Surjective q) : _root_.SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Kan.cubeFiberMax q) :=
  _root_.SerrePositivity.InfinityCategories.Kan.cubeConnectionGenerated_generated (_root_.SerrePositivity.InfinityCategories.Kan.cubeFiberMax_connectionGenerated q hq hs)

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.below (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated.below := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.below

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeConnectionGenerated_generated := _root_.SerrePositivity.InfinityCategories.Kan.cubeConnectionGenerated_generated

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeFiberMax_connectionGenerated := _root_.SerrePositivity.InfinityCategories.Kan.cubeFiberMax_connectionGenerated

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeFiberMax_generated := _root_.SerrePositivity.InfinityCategories.Kan.cubeFiberMax_generated

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated.brecOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.brecOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated.casesOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.comp (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated.comp := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.comp

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.connection (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated.connection := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.connection

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.id (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated.id := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.id

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated.rec := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated.recOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.below.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated.below.casesOn := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.below.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.below.comp (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated.below.comp := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.below.comp

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.below.connection (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated.below.connection := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.below.connection

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.below.id (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated.below.id := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.below.id

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.below.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeConnectionGenerated.below.rec := _root_.SerrePositivity.InfinityCategories.Kan.CubeConnectionGenerated.below.rec
