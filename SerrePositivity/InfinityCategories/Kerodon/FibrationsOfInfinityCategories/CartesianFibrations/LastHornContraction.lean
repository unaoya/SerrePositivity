module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalFiberCofinality

/-!
概要：外側右ホーンの終点を固定する収縮。
方針：標準単体の終点収縮は、最後以外の欠けた頂点を保つのでホーンに制限できる。
規約：ホーンの次元は n+1。内側ホーンについては主張しない。
使われ方：left fibration に沿う外側右ホーンの引き戻しの比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：外側右ホーン内の最後の頂点。
方針：最後の頂点に定値な単体には頂点零が欠ける。
規約：一次ホーンも含む。
使われ方：ホーン上の終点 fiber の指定。 -/
def cofinalLastHornVertex (n : ℕ) :
    (horn (n + 1) (Fin.last (n + 1)) : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), by
    apply (mem_horn_iff_notMem_range _ _).2
    refine ⟨0, ?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at this
      omega
    · rintro ⟨i, hi⟩
      change Fin.last (n + 1) = 0 at hi
      have := congrArg Fin.val hi
      simp only [Fin.val_zero, Fin.val_last] at this
      omega⟩

/-- 概要：標準単体の終点収縮を外側右ホーンに制限する。
方針：入力で欠ける最後以外の頂点は収縮後も欠ける。
規約：時刻零は恒等、時刻一は最後の頂点に定値。
使われ方：ホーンの終点 fiber から全空間への包含の判定。 -/
def cofinalLastHornContraction (n : ℕ) :
    (Δ[1] : SSet.{u}) ⊗ (horn (n + 1) (Fin.last (n + 1)) : SSet.{u}) ⟶
      (horn (n + 1) (Fin.last (n + 1)) : SSet.{u}) where
  app d := ↾fun s ↦ ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction (n + 1)).app d (s.1, s.2.val), by
    obtain ⟨⟨d⟩⟩ := d
    obtain ⟨j, hj, hm⟩ := (mem_horn_iff_notMem_range s.2.val _).1 s.2.property
    apply (mem_horn_iff_notMem_range _ _).2
    refine ⟨j, hj, ?_⟩
    rintro ⟨k, hk⟩
    change (if s.1 k = 0 then s.2.val k else Fin.last (n + 1)) = j at hk
    split_ifs at hk with ht
    · exact hm ⟨k, hk⟩
    · exact hj hk.symm⟩
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    obtain ⟨⟨d⟩⟩ := d
    obtain ⟨⟨e⟩⟩ := e
    apply stdSimplex.ext
    intro k
    rfl

/-- 概要：ホーンの収縮の時刻零は恒等。
方針：部分型の値を取って標準単体の計算に戻す。
規約：厳密な等式。
使われ方：固定した終点収縮の入力。 -/
lemma cofinalLastHornContraction_zero (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ cofinalLastHornContraction n = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro k
  rfl

/-- 概要：ホーンの収縮の時刻一は最後の頂点に定値。
方針：部分型の値を取って終端の分岐を計算する。
規約：指定したホーン内の頂点を使う。
使われ方：固定した終点収縮の入力。 -/
lemma cofinalLastHornContraction_one (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ cofinalLastHornContraction n = SSet.const (cofinalLastHornVertex n) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro k
  rfl

/-- 概要：ホーンの収縮は最後の頂点に定値な全ての族を固定する。
方針：時間の両分岐とも最後の頂点を与える。
規約：パラメータ K は任意。
使われ方：終点 fiber を固定する持ち上げの底の計算。 -/
lemma cofinalLastHornContraction_const (n : ℕ) (K : SSet.{u}) :
    (Δ[1] ◁ (SSet.const (cofinalLastHornVertex n) : K ⟶ _)) ≫
      cofinalLastHornContraction n = SSet.const (cofinalLastHornVertex n) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, s⟩
  apply Subtype.ext
  apply stdSimplex.ext
  intro k
  change (if _ = 0 then Fin.last (n + 1) else Fin.last (n + 1)) = Fin.last (n + 1)
  split_ifs <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
