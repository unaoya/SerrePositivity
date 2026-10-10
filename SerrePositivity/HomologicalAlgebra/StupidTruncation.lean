module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-! # 項ごとの切り詰めと、その比較射

cochain 複体の下端での切り詰めの包含と、上端での切り詰めへの射影を構成する。
下端から離れた次数のホモロジーは、任意の加法関手を施した後も変わらない。
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits HomologicalComplex

namespace SerrePositivity.StupidTruncation

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- 切り詰めで残した二つの項の間では微分は変わらない。 -/
@[reassoc]
lemma d_XIso {ι : Type*} {c : ComplexShape ι} (K : CochainComplex C ℤ)
    (e : c.Embedding (.up ℤ)) [e.IsRelIff] {i j : ι} {i' j' : ℤ}
    (hi : e.f i = i') (hj : e.f j = j') :
    (K.stupidTrunc e).d i' j' ≫ (K.stupidTruncXIso e hj).hom =
      (K.stupidTruncXIso e hi).hom ≫ K.d i' j' := by
  subst hi hj
  simp [stupidTrunc, stupidTruncXIso, extend_d_eq _ _ rfl rfl]

/-- `a` 次以上の項を残す。 -/
noncomputable abbrev above (K : CochainComplex C ℤ) (a : ℤ) :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE a)

noncomputable def aboveXIso (K : CochainComplex C ℤ) (a q : ℤ) (hq : a ≤ q) :
    (above K a).X q ≅ K.X q :=
  K.stupidTruncXIso (ComplexShape.embeddingUpIntGE a) (i := (q - a).toNat) (by simp; omega)

lemma above_isZero_X (K : CochainComplex C ℤ) (a q : ℤ) (hq : q < a) :
    IsZero ((above K a).X q) := by
  apply isZero_stupidTrunc_X
  simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hq

/-- 下端での項ごとの切り詰めの包含。 -/
noncomputable def inclusion (K : CochainComplex C ℤ) (a : ℤ) : above K a ⟶ K where
  f q := if hq : a ≤ q then (aboveXIso K a q hq).hom else 0
  comm' i j hij := by
    by_cases hi : a ≤ i
    · have hj : a ≤ j := by have : i + 1 = j := hij; omega
      rw [dite_eq_left hi, dite_eq_left hj]
      exact (d_XIso K _ _ _).symm
    · exact (above_isZero_X K a i (by omega)).eq_of_src _ _

lemma inclusion_f (K : CochainComplex C ℤ) (a q : ℤ) (hq : a ≤ q) :
    (inclusion K a).f q = (aboveXIso K a q hq).hom := dite_eq_left hq

lemma inclusion_f_isIso (K : CochainComplex C ℤ) (a q : ℤ) (hq : a ≤ q) :
    IsIso ((inclusion K a).f q) := by rw [inclusion_f _ _ _ hq]; infer_instance

/-- 切り詰めの包含は、すべての次数で単射。 -/
instance inclusion_f_mono (K : CochainComplex C ℤ) (a q : ℤ) : Mono ((inclusion K a).f q) := by
  by_cases hq : a ≤ q
  · have := inclusion_f_isIso K a q hq
    infer_instance
  · exact (above_isZero_X K a q (by omega)).mono _

/-- 深い切り詰めをさらに切れば、浅い切り詰めと同型になる。 -/
noncomputable def aboveAboveIso (K : CochainComplex C ℤ) (a b : ℤ) (hab : b ≤ a) :
    above (above K b) a ≅ above K a := by
  let f := stupidTruncMap (inclusion K b) (ComplexShape.embeddingUpIntGE a)
  have hf (q : ℤ) : IsIso (f.f q) := by
    by_cases hq : a ≤ q
    · have := inclusion_f_isIso K b q (hab.trans hq)
      have he : f.f q ≫ (aboveXIso K a q hq).hom =
          (aboveXIso (above K b) a q hq).hom ≫ (inclusion K b).f q :=
        stupidTruncMap_stupidTruncXIso_hom _ _ _
      have : IsIso (f.f q ≫ (aboveXIso K a q hq).hom) := by rw [he]; infer_instance
      exact IsIso.of_isIso_comp_right (f.f q) (aboveXIso K a q hq).hom
    · exact (above_isZero_X (above K b) a q (by omega)).isIso
        (above_isZero_X K a q (by omega)) _
  have := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

section map

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive]

/-- 項ごとの切り詰めは、任意の加法関手と可換である。 -/
noncomputable def mapAboveIso (K : CochainComplex C ℤ) (a : ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (above K a) ≅
      above ((F.mapHomologicalComplex (.up ℤ)).obj K) a := by
  let L := (F.mapHomologicalComplex (.up ℤ)).obj K
  let P := (F.mapHomologicalComplex (.up ℤ)).obj (above K a)
  let f : P ⟶ L := (F.mapHomologicalComplex (.up ℤ)).map (inclusion K a)
  let g := inclusion L a
  let e (q : ℤ) : P.X q ≅ (above L a).X q :=
    if hq : a ≤ q then F.mapIso (aboveXIso K a q hq) ≪≫ (aboveXIso L a q hq).symm
    else (F.map_isZero (above_isZero_X K a q (by omega))).iso
      (above_isZero_X L a q (by omega))
  have he (q : ℤ) : (e q).hom ≫ g.f q = f.f q := by
    by_cases hq : a ≤ q
    · simp only [e, dite_eq_left hq, Iso.trans_hom, Iso.symm_hom, g,
        inclusion_f _ _ _ hq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change F.map (aboveXIso K a q hq).hom = F.map ((inclusion K a).f q)
      rw [inclusion_f _ _ _ hq]
    · exact (F.map_isZero (above_isZero_X K a q (by omega))).eq_of_src _ _
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j _
  apply (cancel_mono (g.f j)).mp
  rw [Category.assoc, ← g.comm, ← Category.assoc, he, f.comm, Category.assoc, he]

end map

/-- `b` 次以下の項を残す。 -/
noncomputable abbrev below (K : CochainComplex C ℤ) (b : ℤ) :=
  K.stupidTrunc (ComplexShape.embeddingUpIntLE b)

noncomputable def belowXIso (K : CochainComplex C ℤ) (b q : ℤ) (hq : q ≤ b) :
    (below K b).X q ≅ K.X q :=
  K.stupidTruncXIso (ComplexShape.embeddingUpIntLE b) (i := (b - q).toNat) (by simp; omega)

lemma below_isZero_X (K : CochainComplex C ℤ) (b q : ℤ) (hq : b < q) :
    IsZero ((below K b).X q) := by
  apply isZero_stupidTrunc_X
  simpa only [ComplexShape.notMem_range_embeddingUpIntLE_iff] using hq

/-- 上端での項ごとの切り詰めへの射影。 -/
noncomputable def projection (K : CochainComplex C ℤ) (b : ℤ) : K ⟶ below K b where
  f q := if hq : q ≤ b then (belowXIso K b q hq).inv else 0
  comm' i j hij := by
    by_cases hj : j ≤ b
    · have hi : i ≤ b := by have : i + 1 = j := hij; omega
      rw [dite_eq_left hi, dite_eq_left hj]
      apply (cancel_epi (belowXIso K b i hi).hom).mp
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      have hd : (below K b).d i j ≫ (belowXIso K b j hj).hom =
          (belowXIso K b i hi).hom ≫ K.d i j := d_XIso K _ _ _
      rw [← hd]
      simp
    · exact (below_isZero_X K b j (by omega)).eq_of_tgt _ _

lemma projection_f (K : CochainComplex C ℤ) (b q : ℤ) (hq : q ≤ b) :
    (projection K b).f q = (belowXIso K b q hq).inv := dite_eq_left hq

lemma projection_f_isIso (K : CochainComplex C ℤ) (b q : ℤ) (hq : q ≤ b) :
    IsIso ((projection K b).f q) := by rw [projection_f _ _ _ hq]; infer_instance

lemma inclusion_projection (K : CochainComplex C ℤ) (a : ℤ) :
    inclusion K a ≫ projection K (a - 1) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hq : a ≤ q
  · exact (below_isZero_X K (a - 1) q (by omega)).eq_of_tgt _ _
  · exact (above_isZero_X K a q (by omega)).eq_of_src _ _

/-- 項ごとの切り詰めによる短複体。 -/
noncomputable def shortComplex (K : CochainComplex C ℤ) (a : ℤ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (inclusion K a) (projection K (a - 1)) (inclusion_projection K a)

/-- 切り詰めの短複体は、各次数では分裂完全である。 -/
noncomputable def splitting (K : CochainComplex C ℤ) (a q : ℤ) :
    ((shortComplex K a).map (HomologicalComplex.eval C (.up ℤ) q)).Splitting := by
  by_cases hq : a ≤ q
  · exact ShortComplex.Splitting.ofIsIsoOfIsZero _ (inclusion_f_isIso K a q hq)
      (below_isZero_X K (a - 1) q (by omega))
  · exact ShortComplex.Splitting.ofIsZeroOfIsIso _ (above_isZero_X K a q (by omega))
      (projection_f_isIso K (a - 1) q (by omega))

section homology

variable {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- 係数変更の平坦性なしで、下端より上のホモロジーは保たれる。 -/
lemma map_inclusion_quasiIsoAt (K : CochainComplex C ℤ) (a q : ℤ) (hq : a < q) :
    QuasiIsoAt ((F.mapHomologicalComplex (.up ℤ)).map (inclusion K a)) q := by
  have hi (i : ℤ) (hi : a ≤ i) : IsIso (F.map ((inclusion K a).f i)) := by
    have := inclusion_f_isIso K a i hi
    infer_instance
  have := hi (q - 1) (by omega)
  have := hi q (by omega)
  have := hi (q + 1) (by omega)
  rw [quasiIsoAt_iff' _ (q - 1) q (q + 1) (by simp) (by simp)]
  let f := (F.mapHomologicalComplex (.up ℤ)).map (inclusion K a)
  let t := (shortComplexFunctor' D (.up ℤ) (q - 1) q (q + 1)).map f
  have : IsIso t.τ₁ := hi (q - 1) (by omega)
  have : IsIso t.τ₂ := hi q (by omega)
  have : IsIso t.τ₃ := hi (q + 1) (by omega)
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono t

/-- 切り詰めの包含が誘導する、係数変更後のホモロジーの同型。 -/
noncomputable def mapHomologyIso (K : CochainComplex C ℤ) (a q : ℤ) (hq : a < q) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (above K a)).homology q ≅
      ((F.mapHomologicalComplex (.up ℤ)).obj K).homology q := by
  have := map_inclusion_quasiIsoAt F K a q hq
  exact isoOfQuasiIsoAt ((F.mapHomologicalComplex (.up ℤ)).map (inclusion K a)) q

end homology
end SerrePositivity.StupidTruncation
