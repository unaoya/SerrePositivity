module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExPairingFaceUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.UniqueFaceNondegenerate

/-!
# Ex pairing の型 II と properness

概要：元の部分対象と前段の像の外の非退化単体に対して properness の条件を証明する。
方針：正次元では前後の面の一意性を使い、零次元では単位の像が全体であることを使う。
規約：Moss 2020 Lemmas 28・29。Mathlib の IsUniquelyCodimOneFace へ接続する。
使われ方：X→Ex(X) の pairing を構成する入力。

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
概要：一つ前の次元からの pairing 候補の像を表す。
方針：正次元では range、零次元では空集合を使う。
規約：Moss 2020 Theorem 22 の型 I の候補の集合。
使われ方：型 II の定義で既に対応先である単体を除く。
-/
def exPairingImage (X : SSet.{u}) : (n : ℕ) → Set ((SSet.ex.obj X) _⦋n⦌)
  | 0 => ∅
  | n + 1 => Set.range (exPairingStep X n)

/--
概要：元の部分対象の外にある非退化単体で、前段の対応先でないもの。
方針：非退化性、単位の像の外、前段の像の外の三条件を明示する。
規約：Moss 2020 Theorem 22 の型 II の定義。
使われ方：pairing の定義域。
-/
def exTypeTwo (X : SSet.{u}) (n : ℕ) : Set ((SSet.ex.obj X) _⦋n⦌) :=
  {s | s ∈ (SSet.ex.obj X).nonDegenerate n ∧
    s ∉ Set.range ((exUnitAt X).app (op ⦋n⦌)) ∧ s ∉ exPairingImage X n}

/--
概要：型 II の単体について、対応先から元へ戻る面は一意である。
方針：正次元の一意性の補題を使い、零次元の型 II の不存在を最小閾値零から示す。
規約：Moss 2020 Lemma 29。
使われ方：pairing の properness と対応先の非退化性。
-/
theorem exPairingStep_face_unique (X : SSet.{u}) (n : ℕ)
    (s : (SSet.ex.obj X) _⦋n⦌) (hs : s ∈ exTypeTwo X n) :
    ∃! i : Fin (n + 2), (SSet.ex.obj X).δ i (exPairingStep X n s) = s := by
  cases n with
  | zero =>
      have hz : exComplexityLevel X ⦋0⦌ s = 0 := by
        apply Fin.ext
        have h := (exComplexityLevel X ⦋0⦌ s).isLt
        change (exComplexityLevel X ⦋0⦌ s).val = 0
        change (exComplexityLevel X ⦋0⦌ s).val < 1 at h
        omega
      exact (hs.2.1 ((exComplexityLevel_zero_iff X _ s).mp hz)).elim
  | succ n => exact exPairingStep_face_unique_succ X n s hs.1 hs.2.1 hs.2.2

/--
概要：型 II の単体の対応先は非退化である。
方針：元が非退化で指定面として一意に現れることを使う。
規約：Moss 2020 Lemma 29。
使われ方：型 I の集合への写像の定義。
-/
theorem exPairingStep_nonDegenerate_target (X : SSet.{u}) (n : ℕ)
    (s : (SSet.ex.obj X) _⦋n⦌) (hs : s ∈ exTypeTwo X n) :
    exPairingStep X n s ∈ (SSet.ex.obj X).nonDegenerate (n + 1) :=
  nonDegenerate_of_unique_face (SSet.ex.obj X) n s (exPairingStep X n s) hs.1
    (exPairingStep_face_unique X n s hs)

/--
概要：型 II の単体は対応先の一意な余次元一の面である。
方針：面の添字の一意性を Mathlib の全単体の述語へ移す。
規約：Moss 2020 Lemma 29 と Mathlib の proper pairing の規約。
使われ方：regular pairing の properness フィールド。
-/
theorem exPairingStep_isUniquelyCodimOneFace (X : SSet.{u}) (n : ℕ)
    (s : (SSet.ex.obj X) _⦋n⦌) (hs : s ∈ exTypeTwo X n) :
    SSet.S.IsUniquelyCodimOneFace (SSet.S.mk s) (SSet.S.mk (exPairingStep X n s)) :=
  (SSet.S.IsUniquelyCodimOneFace.iff _ _).mpr (exPairingStep_face_unique X n s hs)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
