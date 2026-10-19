module

public import SerrePositivity.KST.DerivedGeometry.SmallQuotientComplexFamily
public import SerrePositivity.KST.DerivedGeometry.LeftSmallAcyclicProperties

/-!
概要：生成対象だけから定まる小さい上に有界な非輪状試験複体族を構成する。
方針：統一した固定対象の商を項に持つ小さい複体族の中で、非輪状性と有界性を満たすものを取る。
規約：試験族の存在・小ささは実際の Type と構成した代表の包含で示す。
使われ方：Stacks Lemma 19.12.2・19.12.3、TT §3・§8、Toën §3.2 の非有界 K-injective 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
概要：生成対象に対して定まる非輪状試験複体の小さい添字型。
方針：小さい商の複体データに非輪状性と上に有界な項の零性を課す。
規約：存在命題のフィールドではなく実際の試験族の添字。
使われ方：Stacks 19.12.2・19.12.3、TT §3 の小さい試験集合。
-/
def SmallAcyclicTestIndex (G : C) : Type w :=
  {s : SmallQuotientComplexData (fun _ => smallAcyclicUniformBound G) //
    s.realize.Acyclic ∧ ∃ top : ℤ, ∀ n : ℤ, top < n → IsZero (s.realize.X n)}

/--
概要：小さい添字から実際の非輪状複体を返す試験族。
方針：符号化された商の複体を実現する。
規約：元の複体の圏の対象。
使われ方：Stacks 19.12.3、TT §3 の small object factorization の試験入力。
-/
def smallAcyclicTestFamily (G : C) (s : SmallAcyclicTestIndex G) : CochainComplex C ℤ :=
  s.val.realize

/--
概要：固定した上界で各項を呈示できる上に有界な非輪状複体は試験族の元と同型。
方針：構成済みの小さい商の複体代表へ移し、非輪状性と項の零性を同型で移す。
規約：上界は生成対象だけに依存する固定対象。
使われ方：Stacks 19.12.2・19.12.3、TT §3 の小さい試験集合の包含性。
-/
lemma exists_smallAcyclicTestFamily_iso (G : C) (K : CochainComplex C ℤ)
    (hK : K.Acyclic) (top : ℤ) [K.IsStrictlyLE top]
    (hP : ∀ n, ∃ p : smallAcyclicUniformBound G ⟶ K.X n, Epi p) :
    ∃ s : SmallAcyclicTestIndex G, Nonempty (smallAcyclicTestFamily G s ≅ K) := by
  obtain ⟨s, ⟨e⟩⟩ := exists_smallQuotientComplexData_iso
    (fun _ => smallAcyclicUniformBound G) K hP
  have hs : s.realize.Acyclic := fun n => (hK n).of_iso e.symm
  have hb : ∀ n : ℤ, top < n → IsZero (s.realize.X n) := by
    intro n hn
    exact (K.isZero_of_isStrictlyLE top n hn).of_iso
      ((HomologicalComplex.eval C (.up ℤ) n).mapIso e)
  exact ⟨⟨s, hs, top, hb⟩, ⟨e⟩⟩

/--
概要：構成した小さい非輪状整数部分複体は、固定した試験族の元と同型。
方針：各項の統一した商呈示、有界性、非輪状性を代表包含定理へ渡す。
規約：試験族は元の整数複体や指定した射には依存しない。
使われ方：Stacks 19.12.2・19.12.3、TT §3 の非零部分対象の存在への接続。
-/
lemma leftSmallAcyclicComplex_mem_tests (G : C) (hG : IsSeparator G)
    (M : CochainComplex C ℤ) (hM : M.Acyclic) (top : ℤ)
    (ψ : G ⟶ (M.restriction (ComplexShape.embeddingUpIntLE top)).X 1) :
    ∃ s : SmallAcyclicTestIndex G,
      Nonempty (smallAcyclicTestFamily G s ≅ leftSmallAcyclicComplex G hG M hM top ψ) :=
  exists_smallAcyclicTestFamily_iso G _ (leftSmallAcyclicComplex_acyclic G hG M hM top ψ)
    top (leftSmallAcyclicComplex_term_cover G hG M hM top ψ)

end SerrePositivity.KST.DerivedGeometry
