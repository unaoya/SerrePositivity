module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionLastVertex

/-!
# 非空有限鎖の和集合による作用素の比較

概要：線形順序の非空有限鎖の和を保つ作用素を singleton 上で比較する。
方針：非空有限集合の帰納法により、全体の一致を頂点上の式へ帰着する。
規約：Moss 2020 Lemma 26 の証明で使う binary join に関する議論。
使われ方：細分上の面・退化との交換則を証明する。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder

/--
概要：線形順序の非空有限集合を非空有限鎖として扱う。
方針：線形順序では全ての二元が比較可能である。
規約：Moss 2020 Lemma 26 の有限集合の模型。
使われ方：singleton と和集合の構成。
-/
def finiteChainOfFinset {α : Type u} [LinearOrder α] (s : Finset α) (hs : s.Nonempty) :
    NonemptyFiniteChains α :=
  ⟨s, hs, fun a b => le_total a.val b.val⟩

/--
概要：一つの頂点だけからなる非空有限鎖。
方針：singleton の非空性を使う。
規約：Moss 2020 Lemma 26 の作用素を比較する生成元。
使われ方：和を保つ写像の一致の判定。
-/
def finiteChainSingleton {α : Type u} [LinearOrder α] (a : α) : NonemptyFiniteChains α :=
  finiteChainOfFinset {a} (Finset.singleton_nonempty a)

/--
概要：二つの非空有限鎖の和集合。
方針：線形順序で和集合を再び有限鎖として扱う。
規約：Moss 2020 Lemma 26 の binary join。
使われ方：singleton 上の比較を任意の非空有限集合へ広げる。
-/
def finiteChainUnion {α : Type u} [LinearOrder α] (a b : NonemptyFiniteChains α) :
    NonemptyFiniteChains α :=
  finiteChainOfFinset (a.finset ∪ b.finset) (a.nonempty.mono Finset.subset_union_left)

/--
概要：非空有限鎖の作用素が二元の和集合を保つという条件。
方針：構成した和集合に関する等式で述べる。
規約：Moss 2020 Lemma 26 の計算の前提。追加の公理ではない。
使われ方：作用素の合成と singleton 上の式による比較。
-/
def PreservesFiniteChainUnion {α β : Type u} [LinearOrder α] [LinearOrder β]
    (F : NonemptyFiniteChains α → NonemptyFiniteChains β) : Prop :=
  ∀ a b, F (finiteChainUnion a b) = finiteChainUnion (F a) (F b)

/--
概要：和を保つ二つの作用素は singleton 上で一致すれば全体で一致する。
方針：非空有限集合を singleton と残りの和に分解して帰納する。
規約：Moss 2020 Lemma 26 の全ての交換則に使う比較原理。
使われ方：細分された写像の等式の頂点上の検証。
-/
theorem finiteChainUnion_ext {α β : Type u} [LinearOrder α] [LinearOrder β]
    {F G : NonemptyFiniteChains α → NonemptyFiniteChains β}
    (hF : PreservesFiniteChainUnion F) (hG : PreservesFiniteChainUnion G)
    (h : ∀ a, F (finiteChainSingleton a) = G (finiteChainSingleton a)) : F = G := by
  have heq : ∀ (s : Finset α) (hs : s.Nonempty),
      F (finiteChainOfFinset s hs) = G (finiteChainOfFinset s hs) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro hs; exact (hs.ne_empty rfl).elim
    | @insert a s _ha ih =>
      intro hs
      by_cases hs' : s.Nonempty
      · have hu : finiteChainOfFinset (insert a s) hs =
            finiteChainUnion (finiteChainSingleton a) (finiteChainOfFinset s hs') := by
          apply NonemptyFiniteChains.ext
          ext x
          simp [finiteChainOfFinset, finiteChainSingleton, finiteChainUnion]
        rw [hu, hF, hG, h a, ih hs']
      · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
        subst s
        have hu : finiteChainOfFinset (insert a ∅) hs = finiteChainSingleton a := by
          apply NonemptyFiniteChains.ext
          simp [finiteChainOfFinset, finiteChainSingleton]
        rw [hu]
        exact h a
  funext s
  exact heq s.finset s.nonempty

/--
概要：和を保つ作用素の合成も和を保つ。
方針：二つの保存性を順に適用する。
規約：Moss 2020 Lemma 26 の合成写像の比較。
使われ方：singleton 上の等式による長い合成の検証。
-/
theorem PreservesFiniteChainUnion.comp {α β γ : Type u}
    [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    {F : NonemptyFiniteChains α → NonemptyFiniteChains β}
    {G : NonemptyFiniteChains β → NonemptyFiniteChains γ}
    (hG : PreservesFiniteChainUnion G) (hF : PreservesFiniteChainUnion F) :
    PreservesFiniteChainUnion (G ∘ F) := by
  intro a b
  change G (F (finiteChainUnion a b)) = _
  rw [hF, hG]
  rfl

/--
概要：単調写像による有限鎖の像は和集合を保つ。
方針：集合の像と和集合の交換則を使う。
規約：Moss 2020 Lemma 26 の通常の面・退化の部分。
使われ方：sd(δ) と sd(σ) の singleton 上の比較。
-/
theorem finiteChainMap_preservesUnion {α β : Type u} [LinearOrder α] [LinearOrder β]
    (f : α →o β) : PreservesFiniteChainUnion (fun s => s.map f) := by
  intro a b
  apply NonemptyFiniteChains.ext
  ext x
  simp only [NonemptyFiniteChains.mem_map_iff, finiteChainUnion, finiteChainOfFinset,
    Finset.mem_union]
  aesop

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
