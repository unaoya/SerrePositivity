module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteCochainReduction
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteCochainReduction

/-!
# 指定されたスカラー商による完備複体の比較

## 概要
実際の商複体への射を短完全列で指定し、完備複体の射の擬同型を判定する。

## 方針
二つの商を通常商の関手と余核の一意性で比較し、既存の完備複体の判定を使う。

## 規約
商は選択した余核である必要はない。短完全列と可換四角形を入力にする。

## 使われ方
BS 著者版 Theorem 6.4 の実際の mod p の結晶の橋への適用。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace SerrePositivity.DerivedCompletion

set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] (a : R)

private theorem reductionProjection_natural
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    reductionProjection a K ≫
        ((scalarReductionFunctor a).mapHomologicalComplex (.up ℤ)).map f =
      f ≫ reductionProjection a L := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- 自然数添字の複体を整数添字へ零延長すると、スカラー作用も延長される。 -/
theorem cochain_extendMap_smulId (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex.extendMap (a • 𝟙 K) ComplexShape.embeddingUpNat =
      smulId a (K.extend ComplexShape.embeddingUpNat) := by
  apply HomologicalComplex.Hom.ext
  funext i
  let emb := ComplexShape.embeddingUpNat
  by_cases h : ∃ j, emb.f j = i
  · obtain ⟨j, rfl⟩ := h
    rw [extendMap_f _ emb rfl]
    simp only [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, smulId,
      Linear.comp_smul, Linear.smul_comp, Category.id_comp, Iso.hom_inv_id]
    rfl
  · exact (K.isZero_extend_X emb i (fun j hj => h ⟨j, hj⟩)).eq_of_src _ _

/-- 自然数添字の複体の短完全列は、整数添字への零延長で短完全になる。 -/
theorem cochainShortExact_extend
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact) :
    (S.map (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R))).ShortExact := by
  let emb := ComplexShape.embeddingUpNat
  let T := S.map (emb.extendFunctor (ModuleCat.{u} R))
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases h : ∃ j, emb.f j = i
  · obtain ⟨j, rfl⟩ := h
    let e : S.map (HomologicalComplex.eval (ModuleCat R) (.up ℕ) j) ≅
        T.map (HomologicalComplex.eval (ModuleCat R) (.up ℤ) (emb.f j)) :=
      ShortComplex.isoMk (S.X₁.extendXIso emb rfl).symm
        (S.X₂.extendXIso emb rfl).symm (S.X₃.extendXIso emb rfl).symm
        (by
          change (S.X₁.extendXIso emb rfl).inv ≫ (extendMap S.f emb).f (emb.f j) =
            S.f.f j ≫ (S.X₂.extendXIso emb rfl).inv
          rw [extendMap_f _ emb rfl]
          simp only [Iso.inv_hom_id_assoc])
        (by
          change (S.X₂.extendXIso emb rfl).inv ≫ (extendMap S.g emb).f (emb.f j) =
            S.g.f j ≫ (S.X₃.extendXIso emb rfl).inv
          rw [extendMap_f _ emb rfl]
          simp only [Iso.inv_hom_id_assoc])
    exact ShortComplex.shortExact_of_iso e
      (hS.map_of_exact (HomologicalComplex.eval (ModuleCat R) (.up ℕ) j))
  · have h₁ := S.X₁.isZero_extend_X emb i (fun j hj => h ⟨j, hj⟩)
    have h₂ := S.X₂.isZero_extend_X emb i (fun j hj => h ⟨j, hj⟩)
    have h₃ := S.X₃.isZero_extend_X emb i (fun j hj => h ⟨j, hj⟩)
    have : IsIso ((T.map (HomologicalComplex.eval (ModuleCat R) (.up ℤ) i)).f) :=
      h₁.isIso h₂ _
    have : IsIso ((T.map (HomologicalComplex.eval (ModuleCat R) (.up ℤ) i)).g) :=
      h₂.isIso h₃ _
    exact { exact := ShortComplex.exact_of_isZero_X₂ _ h₂ }

/-- 短完全列で指定された二つのスカラー商の比較から、完備複体の擬同型が従う。 -/
theorem cochain_quasiIso_of_complete_of_scalarQuotient
    {K L QK QL : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (qK : K ⟶ QK) (qL : L ⟶ QL)
    (zK : smulId a K ≫ qK = 0) (zL : smulId a L ≫ qL = 0)
    (hSK : (ShortComplex.mk (smulId a K) qK zK).ShortExact)
    (hSL : (ShortComplex.mk (smulId a L) qL zL).ShortExact)
    (g : QK ⟶ QL) (hcomm : qK ≫ g = f ≫ qL) (hg : QuasiIso g)
    (hK : IsComplete R a (DerivedCategory.Q.obj K))
    (hL : IsComplete R a (DerivedCategory.Q.obj L)) : QuasiIso f := by
  have : Mono (smulId a K) := hSK.mono_f
  have : Mono (smulId a L) := hSL.mono_f
  have : Epi qK := hSK.epi_g
  have : Epi qL := hSL.epi_g
  have hrK (i : ℤ) : Function.Injective (fun x : K.X i => a • x) :=
    (ModuleCat.mono_iff_injective ((smulId a K).f i)).mp inferInstance
  have hrL (i : ℤ) : Function.Injective (fun x : L.X i => a • x) :=
    (ModuleCat.mono_iff_injective ((smulId a L).f i)).mp inferInstance
  have : Epi (reductionShortComplex a K).g :=
    (reductionShortComplex_shortExact a K hrK).epi_g
  have : Epi (reductionShortComplex a L).g :=
    (reductionShortComplex_shortExact a L hrL).epi_g
  let sK := hSK.exact.gIsCokernel
  let sL := hSL.exact.gIsCokernel
  let tK := (reductionShortComplex_shortExact a K hrK).exact.gIsCokernel
  let tL := (reductionShortComplex_shortExact a L hrL).exact.gIsCokernel
  let eK := sK.coconePointUniqueUpToIso tK
  let eL := sL.coconePointUniqueUpToIso tL
  have heK : qK ≫ eK.hom = reductionProjection a K :=
    IsColimit.comp_coconePointUniqueUpToIso_hom sK tK WalkingParallelPair.one
  have heL : qL ≫ eL.hom = reductionProjection a L :=
    IsColimit.comp_coconePointUniqueUpToIso_hom sL tL WalkingParallelPair.one
  let G := (scalarReductionFunctor a).mapHomologicalComplex (.up ℤ)
  have hn : g ≫ eL.hom = eK.hom ≫ G.map f := by
    apply (cancel_epi qK).mp
    calc
      qK ≫ g ≫ eL.hom = (f ≫ qL) ≫ eL.hom := by rw [← Category.assoc, hcomm]
      _ = f ≫ reductionProjection a L := by rw [Category.assoc, heL]
      _ = reductionProjection a K ≫ G.map f := (reductionProjection_natural a f).symm
      _ = qK ≫ eK.hom ≫ G.map f := by rw [← heK, Category.assoc]
  apply cochain_quasiIso_of_complete_of_reduction a f hK hL hrK hrL
  have : QuasiIso (eK.hom ≫ G.map f) := by
    rw [← hn]
    have := hg
    infer_instance
  exact quasiIso_of_comp_left eK.hom _

/-- 自然数添字の複体でも、零延長の完備性と実際の商複体から擬同型を判定できる。 -/
theorem cochainNat_quasiIso_of_complete_of_scalarQuotient
    {K L QK QL : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    (qK : K ⟶ QK) (qL : L ⟶ QL)
    (zK : (a • 𝟙 K) ≫ qK = 0) (zL : (a • 𝟙 L) ≫ qL = 0)
    (hSK : (ShortComplex.mk (a • 𝟙 K) qK zK).ShortExact)
    (hSL : (ShortComplex.mk (a • 𝟙 L) qL zL).ShortExact)
    (g : QK ⟶ QL) (hcomm : qK ≫ g = f ≫ qL) (hg : QuasiIso g)
    (hK : IsComplete R a (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat)))
    (hL : IsComplete R a (DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat))) :
    QuasiIso f := by
  let emb := ComplexShape.embeddingUpNat
  have zK' : smulId a (K.extend emb) ≫ extendMap qK emb = 0 := by
    rw [← cochain_extendMap_smulId, ← extendMap_comp, zK, extendMap_zero]
  have zL' : smulId a (L.extend emb) ≫ extendMap qL emb = 0 := by
    rw [← cochain_extendMap_smulId, ← extendMap_comp, zL, extendMap_zero]
  have hSK' : (ShortComplex.mk (smulId a (K.extend emb)) (extendMap qK emb) zK').ShortExact := by
    have h := cochainShortExact_extend (ShortComplex.mk (a • 𝟙 K) qK zK) hSK
    change (ShortComplex.mk (extendMap (a • 𝟙 K) emb) (extendMap qK emb) _).ShortExact at h
    simpa only [emb, cochain_extendMap_smulId] using h
  have hSL' : (ShortComplex.mk (smulId a (L.extend emb)) (extendMap qL emb) zL').ShortExact := by
    have h := cochainShortExact_extend (ShortComplex.mk (a • 𝟙 L) qL zL) hSL
    change (ShortComplex.mk (extendMap (a • 𝟙 L) emb) (extendMap qL emb) _).ShortExact at h
    simpa only [emb, cochain_extendMap_smulId] using h
  have hcomm' : extendMap qK emb ≫ extendMap g emb = extendMap f emb ≫ extendMap qL emb := by
    rw [← extendMap_comp, hcomm, extendMap_comp]
  have hg' : QuasiIso (extendMap g emb) := by
    have := hg
    infer_instance
  apply (quasiIso_extendMap_iff f emb).mp
  exact cochain_quasiIso_of_complete_of_scalarQuotient a (extendMap f emb)
    (extendMap qK emb) (extendMap qL emb) zK' zL' hSK' hSL' (extendMap g emb) hcomm' hg' hK hL

end SerrePositivity.DerivedCompletion
