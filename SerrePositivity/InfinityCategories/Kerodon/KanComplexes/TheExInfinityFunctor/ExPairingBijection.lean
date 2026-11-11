module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExPairingProperness

/-!
# Ex pairing の次元ごとの全単射

概要：型 II の n 単体と型 I の n+1 単体の全単射を構成する。
方針：対応先の一意性と Moss Lemmas 28・29 の非退化性を使う。
規約：Moss 2020 Theorem 22 の pairing。正則性は別の条件。
使われ方：全次元の非退化単体の分割と Mathlib の pairing の構成。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite
open scoped _root_.Simplicial

/--
概要：単位の像の外の非退化単体で、前段の対応先であるもの。
方針：非退化性、単位の像の外、前段の像への所属を明示する。
規約：Moss 2020 Theorem 22 の型 I。
使われ方：型 II からの全単射の値域。
-/
def exTypeOne (X : SSet.{u}) (n : ℕ) : Set ((SSet.ex.obj X) _⦋n⦌) :=
  {s | s ∈ (SSet.ex.obj X).nonDegenerate n ∧
    s ∉ Set.range ((exUnitAt X).app (op ⦋n⦌)) ∧ s ∈ exPairingImage X n}

/--
概要：型 II の対応先は型 I に属する。
方針：非退化性と単位の像の所属の同値を、前段の像の明示的な表示に合わせる。
規約：Moss 2020 Lemma 29。
使われ方：pairing の写像の well-definedness。
-/
theorem exPairingStep_mem_typeOne (X : SSet.{u}) (n : ℕ)
    (s : (SSet.ex.obj X) _⦋n⦌) (hs : s ∈ exTypeTwo X n) :
    exPairingStep X n s ∈ exTypeOne X (n + 1) := by
  refine ⟨exPairingStep_nonDegenerate_target X n s hs, ?_, ⟨s, rfl⟩⟩
  exact fun h => hs.2.1 ((exPairingStep_mem_image_iff X n s).mp h)

/--
概要：対応先が型 I に属するなら、その元は型 II に属する。
方針：対応先から非退化性と単位の像の外を戻し、二重適用の退化性で前段の像を除く。
規約：Moss 2020 Lemma 28。
使われ方：pairing の全射性。
-/
theorem exPairingStep_mem_typeTwo_of_typeOne (X : SSet.{u}) (n : ℕ)
    (s : (SSet.ex.obj X) _⦋n⦌) (hs : exPairingStep X n s ∈ exTypeOne X (n + 1)) :
    s ∈ exTypeTwo X n := by
  refine ⟨exPairingStep_nonDegenerate_source X n s hs.1, ?_, ?_⟩
  · exact fun h => hs.2.1 ((exPairingStep_mem_image_iff X n s).mpr h)
  · cases n with
    | zero => exact Set.notMem_empty s
    | succ n => exact exPairingStep_notMem_range_of_nonDegenerate X n s hs.1

/--
概要：型 II の n 単体と型 I の n+1 単体の全単射。
方針：最小複雑度の拡張の単射性と、型 I の前段の像による表示を使う。
規約：Moss 2020 Theorem 22 の pairing の次元別の形。
使われ方：全次元の pairing へまとめる。
-/
def exPairingEquiv (X : SSet.{u}) (n : ℕ) : exTypeTwo X n ≃ exTypeOne X (n + 1) :=
  Equiv.ofBijective
    (fun s => ⟨exPairingStep X n s.val, exPairingStep_mem_typeOne X n s.val s.property⟩)
    ⟨fun s t h => Subtype.ext ((exPairingStep_injective X n) (congrArg Subtype.val h)), by
      intro t
      obtain ⟨s, hs⟩ := t.property.2.2
      have ht : exPairingStep X n s ∈ exTypeOne X (n + 1) := hs.symm ▸ t.property
      exact ⟨⟨s, exPairingStep_mem_typeTwo_of_typeOne X n s ht⟩, Subtype.ext hs⟩⟩

/--
概要：次元別の全単射の値は最小複雑度の拡張である。
方針：Equiv.ofBijective の定義を展開する。
規約：Moss 2020 Theorem 22 の対応の計算規約。
使われ方：pairing の面と複雑度を計算する。
-/
theorem exPairingEquiv_apply (X : SSet.{u}) (n : ℕ) (s : exTypeTwo X n) :
    (exPairingEquiv X n s).val = exPairingStep X n s.val := rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
