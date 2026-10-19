module

public import SerrePositivity.KST.DerivedGeometry.SmallQuotientFamily
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
概要：次数ごとの固定対象の商で表せる複体を含む小さい複体族を構成する。
方針：実際の商の代表と微分の射を小さい添字へ符号化し、成分同型で任意の該当複体を移す。
規約：微分とその法則を持つ通常の複体データであり、分解や K-injectivity の存在はフィールドにしない。
使われ方：Stacks Lemma 19.12.2 (079K)、TT §3・§8、Toën §3.2 の非輪状試験集合の小ささ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits Opposite
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
概要：次数ごとの固定対象の商の代表上の複体データの小さい型。
方針：商の添字、微分、次数条件と二乗零の法則を記録する。
規約：分解の存在を含まない、通常の複体の符号化。
使われ方：Stacks 19.12.2、TT §3 の試験複体族の実際の添字。
-/
structure SmallQuotientComplexData (Q : ℤ → C) : Type w where
  term (i : ℤ) : Shrink.{w} (Subobject (op (Q i)))
  d (i j : ℤ) : smallQuotientFamily (Q i) (term i) ⟶ smallQuotientFamily (Q j) (term j)
  shape (i j : ℤ) : ¬ (ComplexShape.up ℤ).Rel i j → d i j = 0
  square (i j k : ℤ) : d i j ≫ d j k = 0

/--
概要：小さい商の複体データが与える実際の非有界複体。
方針：記録された項と微分をそのまま取る。
規約：元のアーベル圏の複体。
使われ方：Stacks 19.12.2、TT §3 の小さい試験族。
-/
def SmallQuotientComplexData.realize {Q : ℤ → C} (s : SmallQuotientComplexData Q) :
    CochainComplex C ℤ where
  X i := smallQuotientFamily (Q i) (s.term i)
  d := s.d
  shape := s.shape
  d_comp_d' i j k _ _ := s.square i j k

/--
概要：各項が指定した固定対象の商なら、小さい複体族の元と同型になる。
方針：商の代表への同型を次数ごとに選び、微分を共役する。
規約：複体全体の同型までを実際に構成する。
使われ方：Stacks 19.12.2、TT §3・§8 の小さい非輪状試験集合。
-/
lemma exists_smallQuotientComplexData_iso (Q : ℤ → C) (K : CochainComplex C ℤ)
    (hQ : ∀ i, ∃ p : Q i ⟶ K.X i, Epi p) :
    ∃ s : SmallQuotientComplexData Q, Nonempty (s.realize ≅ K) := by
  have h (i : ℤ) : ∃ s : Shrink.{w} (Subobject (op (Q i))),
      Nonempty (smallQuotientFamily (Q i) s ≅ K.X i) := by
    obtain ⟨p, hp⟩ := hQ i
    have := hp
    exact exists_smallQuotientFamily_iso p
  choose t ht using h
  let e (i : ℤ) := (ht i).some
  let s : SmallQuotientComplexData Q :=
    { term := t
      d i j := (e i).hom ≫ K.d i j ≫ (e j).inv
      shape i j hij := by rw [K.shape i j hij, zero_comp, comp_zero]
      square i j k := by simp [Category.assoc] }
  refine ⟨s, ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩⟩
  intro i j hij
  dsimp [s, SmallQuotientComplexData.realize]
  simp [Category.assoc]

end SerrePositivity.KST.DerivedGeometry
