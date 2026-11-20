module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.LocalRegularPrincipalGenerator
public import SerrePositivity.AlgebraicGeometry.MatrixMinorIdeal

/-!
概要：KST §5、Stacks 080Z, Lemma 15.8.9 の局所環上の正則単項小行列式の選択。
方針：小行列式の生成集合から単元倍を選び、零でない行列式から選択の単射性を得る。
規約：行列の全体の行・列の型には有限性を仮定しない。
使われ方：選んだ行・列をピボットに並べ直して随伴行列の消去に適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] [IsLocalRing R] {m n : Type*}

/--
概要：局所環で小行列式イデアルが正則単項なら、その生成元の単元倍である単射な行・列選択が存在する。
方針：正則単項イデアルの生成集合から単元倍を選び、行・列の重複による行列式の消滅を除く。
規約：KST §5、Stacks 080Z, Lemma 15.8.9 の正則単項特殊形、零次を含む。
使われ方：純変換の生成元消去のための実際のピボットの存在。
-/
theorem exists_injective_minor_unit_multiple (A : Matrix m n R) (k : ℕ)
    (f : R) (hf : IsRegular f) (hI : matrixMinorIdeal A k = Ideal.span {f}) :
    ∃ (r : Fin k → m) (c : Fin k → n) (u : Rˣ),
      Function.Injective r ∧ Function.Injective c ∧ (A.submatrix r c).det = f * (u : R) := by
  obtain ⟨d, ⟨⟨r, c⟩, rfl⟩, u, hdet⟩ :=
    exists_unit_multiple_of_span_eq_regular_principal _ f hf hI
  change (A.submatrix r c).det = f * (u : R) at hdet
  have hdne : (A.submatrix r c).det ≠ 0 := by
    rw [hdet]
    intro hz
    have hu0 : (u : R) = 0 := hf.left (hz.trans (mul_zero f).symm)
    exact u.ne_zero hu0
  refine ⟨r, c, u, ?_, ?_, hdet⟩
  · intro i j hij
    by_contra hne
    apply hdne
    apply Matrix.det_zero_of_row_eq hne
    ext l
    exact congrArg (fun t => A t (c l)) hij
  · intro i j hij
    by_contra hne
    apply hdne
    apply Matrix.det_zero_of_column_eq hne
    intro l
    exact congrArg (fun t => A (r l) t) hij

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
