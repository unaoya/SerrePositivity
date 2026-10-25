module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroLayerInclusion
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeColumns

/-!
概要：零次元層の実包含の係数は、B の同じ native 零次元列。
方針：評価成分を保つ MC 移送と元の直和包含・正規化射影を照合する。
規約：零 shift の単位を保持して比較する。
使われ方：指定 native 増大の零次元係数を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgBarZeroLayerIndex (s : I _⦋0⦌) : dgCoherentBarLayerIndex I 0 :=
  ⟨⟨⟨0, s⟩, by rw [SSet.nondegenerate_zero]; trivial⟩, rfl⟩

lemma dgBarZeroLayerInclusion_column_f (s : I _⦋0⦌) (x : D) (q : ℤ) :
    ((moduleEvaluation R D x).map
      (Sigma.ι (dgCoherentBarLayerFamily R D G 0) (dgBarZeroLayerIndex s) ≫
        dgBarZeroLayerInclusion R D G)).f q =
      ((moduleEvaluation R D x).map
        (Sigma.ι (dgCoherentBarFamily R D G) ⟨0, s⟩ ≫
          dgCoherentBarNormalizedProjection R D G)).f q := by
  simp only [Functor.map_comp, HomologicalComplex.comp_f, dgBarZeroLayerInclusion_eval_f]
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp,
    dgCoherentBarLayerInclusion_ι]
  erw [← HomologicalComplex.comp_f, ← Functor.map_comp,
    dgCoherentBarNormalizedProjection_ι R D G (dgBarZeroLayerIndex s).val]

lemma dgBarZeroLayerInclusion_nativeColumn (s : I _⦋0⦌) :
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D G ⟨0, s⟩))
      (Sigma.ι (dgCoherentBarLayerFamily R D G 0) (dgBarZeroLayerIndex s) ≫
        dgBarZeroLayerInclusion R D G)).f 0
      (moduleShiftInElement R D 0 (dgCoherentBarSource R D G ⟨0, s⟩)) =
        dgCoherentBarNativeColumn R D G (dgCoherentBarMaurerCartan_unconditional R D G) ⟨0, s⟩ := by
  apply moduleHomElement_ext R D
  intro x
  apply Cochain.ext
  intro q r hqr
  subst r
  dsimp only [dgCoherentBarNativeColumn, dgCoherentBarNormalizedShiftedInclusion,
    dgCoherentBarShiftedInclusion]
  simp only [Nat.cast_zero, Int.neg_zero, Int.negOnePow_zero, one_smul]
  erw [dgCoherentBarNormalizedTargetRebase_π]
  erw [moduleHomWhiskerLeft_apply_π, moduleHomWhiskerLeft_apply_π,
    moduleHomWhiskerLeft_apply_π]
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    dgBarZeroLayerInclusion_column_f, Functor.map_comp, HomologicalComplex.comp_f,
    Category.assoc]
  have he := dgBarZeroLayerInclusion_column_f R D G s x (q + 0)
  simp only [Functor.map_comp, HomologicalComplex.comp_f] at he
  erw [he]
  rfl

end SerrePositivity.InfinityCategories
