module

public import SerrePositivity.CommutativeAlgebra.DirectLimitFlat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.Maps
/-! # 通常の忠実平坦性の環余極限による保存

BS Thm 7.14（著者版 p.61）の極限段の忠実性に使う一般論。
固定基底の代数の有向系を扱い、単位元を保つ遷移射であることを利用する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {A ι : Type u} [CommRing A] [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[A] S j) [DirectedSystem S (fun i j h ↦ f i j h)]
/-- 線形写像は I 倍の部分加群を I 倍の部分加群へ送る。
BS Thm 7.14（著者版 p.61）の極限段の補助計算。生成元と加法に関する帰納法による。 -/
private lemma map_ideal_smul {P Q : Type u} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (I : Ideal A) (g : P →ₗ[A] Q) {x : P}
    (hx : x ∈ I • (⊤ : Submodule A P)) : g x ∈ I • (⊤ : Submodule A Q) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr x _
    rw [g.map_smul]
    exact Submodule.smul_mem_smul hr (Submodule.mem_top)
  · intro x y hx hy
    rw [g.map_add]
    exact Submodule.add_mem _ hx hy

/-- ## 概要
代数の有向余極限で基底イデアルの倍として表される元は、一段でも同じイデアルの倍として表せる。
BS Thm 7.14（著者版 p.61）の極限段で忠実性を反映するための補題。

## 方針
部分加群の生成に関する帰納法を用い、加法の場合には二段の共通上界を取る。

## 規約
基底イデアルは有限生成でなくてよく、遷移写像の単射性も不要。
係数は最初の基底 A 上の作用のまま扱う。

## 使われ方
単位元が基底イデアルの拡張に入る関係を有限段に降ろす。
-/
theorem directLimit_mem_ideal_smul (I : Ideal A) (x : _root_.DirectLimit S f)
    (hx : x ∈ I • (⊤ : Submodule A (_root_.DirectLimit S f))) :
    ∃ (i : ι) (y : S i), y ∈ I • (⊤ : Submodule A (S i)) ∧
      DirectLimit.Algebra.of S f i y = x := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr x _
    obtain ⟨i, y, hy⟩ := DirectLimit.exists_eq_mk f x
    refine ⟨i, r • y, Submodule.smul_mem_smul hr (Submodule.mem_top), ?_⟩
    rw [map_smul]
    congr 1
    with_unfolding_all exact hy.symm
  · intro x y hx hy
    obtain ⟨i, a, ha, hax⟩ := hx
    obtain ⟨j, b, hb, hby⟩ := hy
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, f i k hik a + f j k hjk b,
      Submodule.add_mem _ (map_ideal_smul I (f i k hik).toLinearMap ha)
        (map_ideal_smul I (f j k hjk).toLinearMap hb), ?_⟩
    rw [map_add, DirectLimit.Algebra.of_f, DirectLimit.Algebra.of_f, hax, hby]


/-- ## 概要
固定基底 A 上忠実平坦な代数の有向余極限は A 上忠実平坦である。
BS Thm 7.14（著者版 p.61）の極限段の剰余環に用いる一般論。

## 方針
通常平坦性は既存の余極限定理による。基底イデアルの拡張に単位元が入れば、
その表示と単位元との等式を有限段へ降ろし、その段の忠実平坦性から元のイデアルが単位イデアルと示す。

## 規約
遷移射は A 代数準同型で単位元を保つ。一般の加群準同型の有向系については主張しない。
単射性・Noether 性・非零性は要求しない。

## 使われ方
各段の剰余テンソル代数の通常の忠実平坦性から、剰余余極限の忠実平坦性を検証する。
p 完全忠実平坦性そのものや完備化による保存はまだ結論しない。
-/
theorem faithfullyFlat_algebraDirectLimit (hS : ∀ i, Module.FaithfullyFlat A (S i)) :
    Module.FaithfullyFlat A (_root_.DirectLimit S f) := by
  have (i : ι) : Module.Flat A (S i) := (hS i).toFlat
  apply (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top A _).mpr
  refine ⟨directLimit_flat S f, ?_⟩
  intro I hI
  have hmem : (1 : _root_.DirectLimit S f) ∈ I • (⊤ : Submodule A (_root_.DirectLimit S f)) := by
    rw [hI]
    trivial
  obtain ⟨i, x, hx, heq⟩ := directLimit_mem_ideal_smul S f I 1 hmem
  have hz : DirectLimit.Module.of A ι S f i (x - 1) = 0 := by
    change DirectLimit.Ring.of S f i (x - 1) = 0
    rw [map_sub, map_one]
    change DirectLimit.Algebra.of S f i x - 1 = 0
    rw [heq, sub_self]
  obtain ⟨j, hij, hj⟩ := (DirectLimit.exists_eq_zero (f := f) ⟨i, x-1⟩).mp hz
  have he : f i j hij x = 1 := sub_eq_zero.mp (by simpa only [map_sub, map_one] using hj)
  have hm : (1 : S j) ∈ I • (⊤ : Submodule A (S j)) := by
    rw [← he]
    exact map_ideal_smul I (f i j hij).toLinearMap hx
  have htop : I.map (algebraMap A (S j)) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] using hm
  have ht : I • (⊤ : Submodule A (S j)) = ⊤ := by
    rw [Ideal.smul_top_eq_map, htop]
    rfl
  exact ((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top A (S j)).mp (hS j)).2 I ht
end SerrePositivity.BhattScholze.Andre.Transfinite
