module

public import SerrePositivity.AlgebraicGeometry.AdicCompletionSection
public import SerrePositivity.AlgebraicGeometry.CompletedFreeMittagLeffler

/-!
概要：KST §5、Stacks 05DK, Lemma 38.8.2 の平坦加群の完備化の Mittag–Leffler 性。
方針：元の加群への自由全射を完備化し、構成した線形右逆で自由完備化の直和因子とする。
規約：基礎環は完備な Noether 環。最初の剰余にだけ射影性を仮定する。
使われ方：Stacks 05DP の完備化による Mittag–Leffler 性の入力。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：完備な Noether 環上の平坦加群は、最初の剰余が射影的なら完備化が Mittag–Leffler。
方針：元の加群への自由全射の完備化の線形右逆から、自由完備化の性質を降下する。
規約：KST §5、Stacks 05DK, Lemma 38.8.2、加群の有限生成性を要求しない。
使われ方：元の加群から完備化への普遍単射性と合わせた射影性の原典経路。
-/
theorem isModuleMittagLeffler_adicCompletion_of_projective_reduction
    {R M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (I : Ideal R) [IsAdicComplete I R]
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    IsModuleMittagLeffler R (AdicCompletion I M) := by
  let π := Finsupp.linearCombination R (id : M → M)
  have hπ : Function.Surjective π :=
    Finsupp.linearCombination_surjective R Function.surjective_id
  obtain ⟨σ, hσ⟩ := exists_adicCompletion_section_of_flat_of_projective_reduction π hπ I
  exact isModuleMittagLeffler_of_split σ ((AdicCompletion.map I π).restrictScalars R) hσ
    (isModuleMittagLeffler_completedFree I M)

/--
概要：完備な Noether 環上で、剰余が射影的な平坦加群の完備化は平坦 Mittag–Leffler。
方針：既存の完備化の平坦性と、構成した自由完備化の直和因子としての降下を合わせる。
規約：KST §5、Stacks 05DK, Lemma 38.8.2、実際の加群の完備化に関する結論。
使われ方：代数の射影性の存在を証明する完備化側の入力。
-/
theorem flat_mittagLeffler_adicCompletion_of_projective_reduction
    {R M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (I : Ideal R) [IsAdicComplete I R]
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.Flat R (AdicCompletion I M) ∧ IsModuleMittagLeffler R (AdicCompletion I M) :=
  ⟨SerrePositivity.flat_adicCompletion_of_flat I,
    isModuleMittagLeffler_adicCompletion_of_projective_reduction I⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
