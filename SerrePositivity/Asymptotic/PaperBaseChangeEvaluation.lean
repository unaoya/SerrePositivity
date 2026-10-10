module

public import SerrePositivity.Asymptotic.BaseChangeComparison
public import SerrePositivity.Asymptotic.KoszulBaseChange

/-! # 係数変更後の長さによる論文の圏の評価と公式 (4.2) -/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents Filter

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S) {e : ℕ} (z : Fin e → R)

/-- 商でパラメータの冪が零なら、係数変更した実際の複体列の像でも零。 -/
lemma paperBaseChange_complex_smul_zero
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (v : ℕ)
    (hx : ∀ j, z j ^ v • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0) :
    ∀ j, (φ (z j)) ^ v • 𝟙 (completedSequenceFunctor.obj
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK))) = 0 := by
  intro j
  let E := (paperRankEquivalence R s).functor
  let F := completedChangeRing (s := s) φ
  have h0 : z j ^ v • 𝟙 (E.obj ((paperSequenceFunctor R s).obj
      (sequenceHomotopyObj K hK))) = 0 := by
    simpa only [E.map_smul, E.map_id, E.map_zero] using E.congr_map (hx j)
  have h1 := smul_id_zero_of_iso ((paperSequenceComparison R s).app
    (sequenceHomotopyObj K hK)) (z j ^ v) h0
  have h2 := F.congr_map h1
  rw [completedChangeRing_map_smul_id, map_pow, F.map_zero] at h2
  exact smul_id_zero_of_iso ((completedChangeRingFactors φ).app
    (sequenceHomotopyObj K hK)) (φ (z j) ^ v) h2

/-- 実際の複体列において、論文側の係数変更と行列の係数変更が一致する。 -/
noncomputable def paperBaseChangeComplexIso
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (hL : scalarSupported (φ ∘ z) (completedSequenceFunctor.obj
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK)))) :
    (paperSupportedRankEquivalence (φ ∘ z)).functor.obj
      ((paperSupportedChangeRing φ z).obj
        ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) ≅
    completedComplexObj (φ ∘ z)
      (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
      (changeRing_strictlyBounded φ K hK) hL :=
  (paperChangeRingToCompletedIso φ z).app _ ≪≫
    ObjectProperty.isoMk _ ((completedChangeRing φ).mapIso
      ((paperSequenceComparison R s).app (sequenceHomotopyObj K hK)) ≪≫
        (completedChangeRingFactors φ).app (sequenceHomotopyObj K hK))

variable {I : Ideal S} (lam : NormalizedLength S I) (hfg : I.FG)
  (hI : I ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ φ (z j) ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- T → C の後のホモロジーを測る命題4.3の Hᶜ。 -/
noncomputable abbrev paperBaseChangeHomology (q : ℤ) :
    (paperSupportedRank (s := s) z).FullSubcategory ⥤ LengthSerreQuotient lam s U hU hs :=
  paperSupportedChangeRing φ z ⋙ paperRankHomology lam hfg (φ ∘ z) hI hfin U hU hs q

instance paperBaseChangeHomology_isHomological (q : ℤ) :
    (paperBaseChangeHomology φ z lam hfg hI hfin U hU hs q).IsHomological := by infer_instance

noncomputable abbrev paperBaseChangeBetti
    (X : (paperSupportedRank (s := s) z).FullSubcategory) (q : ℤ) : ℝ :=
  paperRankBetti lam hfg (φ ∘ z) hI hfin U hU hs ((paperSupportedChangeRing φ z).obj X) q

lemma paperBaseChangeBetti_nonneg
    (X : (paperSupportedRank (s := s) z).FullSubcategory) (q : ℤ) :
    0 ≤ paperBaseChangeBetti φ z lam hfg hI hfin U hU hs X q := paperRankBetti_nonneg ..

lemma paperBaseChangeBetti_hasFiniteSupport
    (X : (paperSupportedRank (s := s) z).FullSubcategory) :
    Function.HasFiniteSupport (paperBaseChangeBetti φ z lam hfg hI hfin U hU hs X) :=
  paperRankBetti_hasFiniteSupport ..

/-- 支持つきランク商での同型は、係数変更後の各次数の評価を保つ。 -/
lemma paperBaseChangeBetti_iso
    {X Y : (paperSupportedRank (s := s) z).FullSubcategory} (i : X ≅ Y) (q : ℤ) :
    paperBaseChangeBetti φ z lam hfg hI hfin U hU hs X q =
      paperBaseChangeBetti φ z lam hfg hI hfin U hU hs Y q :=
  completedRankBetti_iso lam hfg (φ ∘ z) hI hfin U hU hs
    ((paperSupportedRankEquivalence (φ ∘ z)).functor.mapIso
      ((paperSupportedChangeRing φ z).mapIso i)) q

noncomputable def paperBaseChangeEulerK0 :
    TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory →+ ℝ :=
  (paperRankEulerK0 lam hfg (φ ∘ z) hI hfin U hU hs).comp
    (TriangulatedK0.map (paperSupportedChangeRing φ z))

lemma paperBaseChangeEulerK0_mk (X : (paperSupportedRank (s := s) z).FullSubcategory) :
    paperBaseChangeEulerK0 φ z lam hfg hI hfin U hU hs (TriangulatedK0.mk X) =
      ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) *
        paperBaseChangeBetti φ z lam hfg hI hfin U hU hs X q := by
  rw [paperBaseChangeEulerK0, AddMonoidHom.comp_apply, TriangulatedK0.map_mk,
    paperRankEulerK0_mk]

set_option maxHeartbeats 800000 in
-- 二つの係数環にわたる支持部分圏と局所化の型の比較に必要。
/-- 正規化評価版の公式 (4.2)。元の列の一様支持は仮定しない。 -/
theorem paperBaseChangeBetti_koszul_formula
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0)
    (i : ℤ) :
    normalizedLimit U s (fun n ↦ (lam.len
      ((koszulComplexOn (fun j ↦ φ (z j) ^ v)
        (baseChange φ ((evaluateComplex n).obj K))).homology (-i))).toReal) =
      ∑ j ∈ Finset.range (e + 1), (e.choose j : ℝ) *
        paperBaseChangeBetti φ z lam hfg hI hfin U hU hs
          ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ (-(i - j)) := by
  let L := ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K
  let hL := changeRing_strictlyBounded φ K hK
  have hxL := paperBaseChange_complex_smul_zero φ z K hK v hx
  let h' : scalarSupported (φ ∘ z) (completedSequenceFunctor.obj (sequenceHomotopyObj L hL)) :=
    ⟨v, hv, hxL⟩
  have he := completedRankBetti_koszul_formula (φ ∘ z) lam hfg hI hfin U hU hs
    L hL h' v hv hxL i
  have hn : (fun n ↦ (lam.len ((koszulComplexOn (fun j ↦ φ (z j) ^ v)
        (baseChange φ ((evaluateComplex n).obj K))).homology (-i))).toReal) =
      (fun n ↦ (lam.len ((koszulComplexOn (fun j ↦ (φ ∘ z) j ^ v)
        ((evaluateComplex n).obj L)).homology (-i))).toReal) := by
    funext n
    exact congrArg ENNReal.toReal (lam.len_congr _ _
      (((HomologicalComplex.homologyFunctor _ _ (-i)).mapIso
        ((koszulFunctor (fun j ↦ φ (z j) ^ v)).mapIso
          (FreeSequence.evaluateComplexTensorIso φ n K))).toLinearEquiv))
  rw [hn]
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact (completedRankBetti_iso lam hfg (φ ∘ z) hI hfin U hU hs
    (paperBaseChangeComplexIso φ z K hK h h') _).symm

/-- 元の Koszul 複体をさらに S にテンソルする、論文と同じ右辺での公式 (4.2)。 -/
theorem paperBaseChangeBetti_koszul_tensor_formula
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0)
    (i : ℤ) :
    normalizedLimit U s (fun n ↦ (lam.len
      ((baseChange φ (koszulComplexOn (fun j ↦ z j ^ v)
        ((evaluateComplex n).obj K))).homology (-i))).toReal) =
      ∑ j ∈ Finset.range (e + 1), (e.choose j : ℝ) *
        paperBaseChangeBetti φ z lam hfg hI hfin U hU hs
          ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ (-(i - j)) := by
  have hn : (fun n ↦ (lam.len ((baseChange φ (koszulComplexOn (fun j ↦ z j ^ v)
        ((evaluateComplex n).obj K))).homology (-i))).toReal) =
      (fun n ↦ (lam.len ((koszulComplexOn (fun j ↦ φ (z j) ^ v)
        (baseChange φ ((evaluateComplex n).obj K))).homology (-i))).toReal) := by
    funext n
    have hx' : φ ∘ (fun j ↦ z j ^ v) = (fun j ↦ φ (z j) ^ v) := by ext j; simp
    exact congrArg ENNReal.toReal (lam.len_congr _ _
      (((HomologicalComplex.homologyFunctor _ _ (-i)).mapIso
        (baseChangeKoszulOnIso φ (fun j ↦ z j ^ v) ((evaluateComplex n).obj K) ≪≫
          eqToIso (congrArg (fun x ↦ koszulComplexOn x
            (baseChange φ ((evaluateComplex n).obj K))) hx'))).toLinearEquiv))
  rw [hn]
  exact paperBaseChangeBetti_koszul_formula φ z lam hfg hI hfin U hU hs K hK h v hv hx i

end SerrePositivity.Asymptotic
