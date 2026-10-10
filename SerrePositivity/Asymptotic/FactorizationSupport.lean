module

public import SerrePositivity.Asymptotic.SequenceSupport
public import SerrePositivity.Asymptotic.PaperRankQuotient

/-! # 小さいランクの複体を経由するスカラー作用

各段の因子分解を組み戻し、ホモトピー圏での因子分解を得る。
経由する複体がランク商で零なら、元のスカラー作用も商で零になる。
-/

@[expose] public section

universe u v w

namespace SerrePositivity.Asymptotic

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}

omit [Nontrivial R] in
/-- 段ごとの因子分解を自由列のホモトピーに組み戻す。 -/
lemma assemble_scalar_factorization
    (K G : CochainComplex (FreeSequence R s) ℤ) (r : R)
    (h : ∀ n, ∃ (u : (evaluateComplex n).obj K ⟶ (evaluateComplex n).obj G)
      (v : (evaluateComplex n).obj G ⟶ (evaluateComplex n).obj K),
      Nonempty (Homotopy (r • 𝟙 _) (u ≫ v))) :
    ∃ (u : K ⟶ G) (v : G ⟶ K), Nonempty (Homotopy (r • 𝟙 K) (u ≫ v)) := by
  choose u v h using h
  refine ⟨assembleChainMap u, assembleChainMap v, (nonempty_homotopy_iff _ _).2 ?_⟩
  intro n
  have : (evaluateComplex (R := R) (s := s) n).Linear R := by
    change ((FreeSequence.evaluation n).mapHomologicalComplex (.up ℤ)).Linear R
    infer_instance
  simpa only [Functor.map_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_comp, evaluate_assembleChainMap] using h n

omit [Nontrivial R] in
/-- 経由する複体の像が零なら、ホモトピックなスカラー作用の像も零。 -/
lemma scalar_zero_of_factorization
    {D : Type w} [Category.{v} D] [Preadditive D] [Linear R D]
    (T : SequenceHomotopy R s ⥤ D) [T.Linear R] [T.Additive]
    (K G : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (hG : strictlyBoundedComplex (FreeSequence R s) G)
    (hz : IsZero (T.obj (sequenceHomotopyObj G hG)))
    (r : R) (u : K ⟶ G) (v : G ⟶ K) (h : Homotopy (r • 𝟙 K) (u ≫ v)) :
    r • 𝟙 (T.obj (sequenceHomotopyObj K hK)) = 0 := by
  let u' : sequenceHomotopyObj K hK ⟶ sequenceHomotopyObj G hG :=
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map u)
  let v' : sequenceHomotopyObj G hG ⟶ sequenceHomotopyObj K hK :=
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map v)
  have he : r • 𝟙 (sequenceHomotopyObj K hK) = u' ≫ v' := by
    apply ObjectProperty.hom_ext
    change r • 𝟙 _ = (HomotopyCategory.quotient _ _).map u ≫
      (HomotopyCategory.quotient _ _).map v
    have ht := HomotopyCategory.eq_of_homotopy _ _ h
    simp only [Functor.map_smul, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_comp] at ht
    exact ht
  calc
    _ = T.map (r • 𝟙 (sequenceHomotopyObj K hK)) := by simp
    _ = T.map u' ≫ T.map v' := by rw [he, T.map_comp]
    _ = 0 := by rw [hz.eq_zero_of_tgt (T.map u'), zero_comp]

/-- 小さいランクの複体を経由する作用は、論文の商・完備化の順序でも零になる。 -/
lemma paper_scalar_zero_of_small_factorization
    (K G : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K) (hG : rankSmallComplex G)
    (r : R) (u : K ⟶ G) (v : G ⟶ K) (h : Homotopy (r • 𝟙 K) (u ≫ v)) :
    r • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0 := by
  apply scalar_zero_of_factorization (paperSequenceFunctor R s) K G hK hG.1 _ r u v h
  apply karoubiFirstFromOriginal_kills
  exact ⟨(HomotopyCategory.quotient _ _).obj G,
    (rankSmallHomotopy_quotient G).2 hG, ⟨Iso.refl _⟩⟩

end SerrePositivity.Asymptotic
