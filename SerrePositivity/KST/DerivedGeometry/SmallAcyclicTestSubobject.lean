module

public import SerrePositivity.KST.DerivedGeometry.SmallAcyclicTestFamily
public import Mathlib.CategoryTheory.Generator.Preadditive

/-!
概要：任意の非零な非輪状複体は、固定した小さい試験族に属する非零部分複体を持つ。
方針：非零成分への生成対象からの射を取り、その像を含む構成済みの部分複体を代表族へ移す。
規約：小さい試験部分対象の存在を実際に証明する。
使われ方：Stacks Lemma 19.12.2・19.12.3、TT §3・§8、Toën §3.2 の超限分解の後続段階。
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
概要：生成対象からの指定した射は、試験族の元からの単射を経由する。
方針：構成した部分複体の代表同型へ包含と因子を合成する。
規約：試験族は生成対象だけに依存する。
使われ方：Stacks 19.12.2、TT §3 の非零試験部分対象の検出。
-/
lemma exists_smallAcyclicTest_mono_factor (G : C) (hG : IsSeparator G)
    (M : CochainComplex C ℤ) (hM : M.Acyclic) (top : ℤ)
    (ψ : G ⟶ (M.restriction (ComplexShape.embeddingUpIntLE top)).X 1) :
    ∃ (s : SmallAcyclicTestIndex G) (i : smallAcyclicTestFamily G s ⟶ M)
      (p : G ⟶ (smallAcyclicTestFamily G s).X ((ComplexShape.embeddingUpIntLE top).f 1)),
      Mono i ∧ p ≫ i.f ((ComplexShape.embeddingUpIntLE top).f 1) = ψ := by
  obtain ⟨s, ⟨e⟩⟩ := leftSmallAcyclicComplex_mem_tests G hG M hM top ψ
  obtain ⟨p, hp⟩ := leftSmallAcyclicComplex_factor G hG M hM top ψ
  let j := leftSmallAcyclicComplexInclusion G hG M hM top ψ
  let n := (ComplexShape.embeddingUpIntLE top).f 1
  refine ⟨s, e.hom ≫ j, p ≫ e.inv.f n, inferInstance, ?_⟩
  change (p ≫ e.inv.f n) ≫ (e.hom ≫ j).f n = ψ
  calc
    _ = p ≫ (e.inv ≫ e.hom).f n ≫ j.f n := by simp only [HomologicalComplex.comp_f, Category.assoc]
    _ = p ≫ j.f n := by
      rw [e.inv_hom_id]
      change p ≫ (𝟙 _ ≫ j.f n) = p ≫ j.f n
      rw [Category.id_comp]
    _ = ψ := hp

/--
概要：非零な複体のいずれかの項へ、生成対象から非零射が存在する。
方針：全ての射が零なら各項の恒等射が生成性で零となり、複体が零となる。
規約：微分の完全性はこの検出補題では不要。
使われ方：Stacks 19.12.2、TT §3 の非零な試験部分対象の始点。
-/
lemma exists_nonzero_generator_component (G : C) (hG : IsSeparator G)
    (M : CochainComplex C ℤ) (hM : ¬ IsZero M) :
    ∃ (n : ℤ) (ψ : G ⟶ M.X n), ψ ≠ 0 := by
  classical
  by_contra! h
  apply hM
  rw [IsZero.iff_id_eq_zero]
  ext n
  change 𝟙 (M.X n) = 0
  apply (Preadditive.isSeparator_iff G).mp hG
  intro ψ
  simpa only [Category.comp_id] using h n ψ

/--
概要：非零な非輪状複体には、固定した小さい非輪状試験族からの非零部分対象が存在する。
方針：非零成分への生成対象からの射を小さい部分複体で因子化する。
規約：部分複体の非零性も成分の因子化から証明する。
使われ方：Stacks 19.12.2・19.12.3、TT §3 の小さい商を加える超限工程。
-/
lemma exists_nonzero_smallAcyclicTest_subobject (G : C) (hG : IsSeparator G)
    (M : CochainComplex C ℤ) (hM : M.Acyclic) (hne : ¬ IsZero M) :
    ∃ (s : SmallAcyclicTestIndex G) (i : smallAcyclicTestFamily G s ⟶ M),
      Mono i ∧ ¬ IsZero (smallAcyclicTestFamily G s) := by
  obtain ⟨n, ψ, hψ⟩ := exists_nonzero_generator_component G hG M hne
  let e := ComplexShape.embeddingUpIntLE (n + 1)
  have hi : e.f 1 = n := by change (n + 1) - (1 : ℤ) = n; omega
  let E := M.restrictionXIso e hi
  let ψ' := ψ ≫ E.inv
  have hψ' : ψ' ≠ 0 := by
    intro h
    apply hψ
    apply (cancel_mono E.inv).mp
    simpa only [ψ', zero_comp] using h
  obtain ⟨s, i, p, hi', hp⟩ := exists_smallAcyclicTest_mono_factor G hG M hM (n + 1) ψ'
  refine ⟨s, i, hi', ?_⟩
  intro hs
  have ht := (HomologicalComplex.eval C (.up ℤ) (e.f 1)).map_isZero hs
  have hp0 : p = 0 := ht.eq_zero_of_tgt p
  exact hψ' (by rw [hp0, zero_comp] at hp; exact hp.symm)

end SerrePositivity.KST.DerivedGeometry
