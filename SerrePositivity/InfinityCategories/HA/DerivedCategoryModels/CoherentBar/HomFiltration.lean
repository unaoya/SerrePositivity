module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.MaurerCartanDescent
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Module
/-!
概要：全次数 Hom の標的単体次数による加群フィルトレーションを定める。
方針：次数上限内の因子への射を直和包含で送り、その像部分加群の上限を取る。
規約：有限支持の線形結合を部分加群の上限で扱い、無限和は作らない。
使われ方：段階的正規化の単体次数に関する支持と安定化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarHomFiltration (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (q : ℤ) (n : ℕ) :
    Submodule R ((_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X q) :=
  ⨆ s : {s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I // s.1 ≤ n},
    LinearMap.range ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val)).f q).hom

set_option maxHeartbeats 800000 in
-- 直和 Hom end の像部分加群と、同じ全 Hom の明示型の照合に限った局所上限。
lemma dgCoherentBarHomFiltration_inclusion (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (q : ℤ)
    (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) (hs : s.1 ≤ n)
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))).X q) :
    (eHomWhiskerLeft (Complex R) M (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)).f q f ∈
      dgCoherentBarHomFiltration R D F M q n :=
  Submodule.mem_iSup_of_mem
    (p := fun t : {t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I // t.1 ≤ n} =>
      LinearMap.range ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) t.val)).f q).hom)
    (⟨s, hs⟩ : {s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I // s.1 ≤ n}) ⟨f, rfl⟩

lemma dgCoherentBarHomFiltration_mono (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (q : ℤ)
    {n m : ℕ} (h : n ≤ m) :
    dgCoherentBarHomFiltration R D F M q n ≤ dgCoherentBarHomFiltration R D F M q m := by
  apply iSup_le
  intro s
  rintro _ ⟨f, rfl⟩
  exact dgCoherentBarHomFiltration_inclusion R D F M q m s.val (s.property.trans h) f

lemma dgCoherentBarHomFiltration_compose {L M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} {p q k : ℤ}
    {n : ℕ}
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) L)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)).X p)
    (g : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X q)
    (hg : g ∈ dgCoherentBarHomFiltration R D F M q n) (hk : p + q = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) L)
      (y := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) g f hk ∈
      dgCoherentBarHomFiltration R D F L k n := by
  refine Submodule.iSup_induction
    (motive := fun z => _root_.SerrePositivity.DifferentialGraded.compose R (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) L)
      (y := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) z f hk ∈
        dgCoherentBarHomFiltration R D F L k n)
    (fun s : {s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I // s.1 ≤ n} =>
      LinearMap.range ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val)).f q).hom) hg ?_ ?_ ?_
  · intro s g hg
    obtain ⟨a, rfl⟩ := hg
    rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_postcompose_comp R D]
    exact dgCoherentBarHomFiltration_inclusion R D F L k n s.val s.property _
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]
    exact Submodule.zero_mem _
  · intro a b ha hb
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left]
    exact Submodule.add_mem _ ha hb

lemma dgCoherentBarHomFiltration_postcompose {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} {p q k : ℤ}
    {n m : ℕ}
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X p)
    (g : (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X q)
    (hf : f ∈ dgCoherentBarHomFiltration R D F M p n)
    (hg : ∀ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I, s.1 ≤ n →
      (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f q g ∈
        dgCoherentBarHomFiltration R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s) q m)
    (hk : p + q = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) g f hk ∈
      dgCoherentBarHomFiltration R D F M k m := by
  refine Submodule.iSup_induction
    (motive := fun z => _root_.SerrePositivity.DifferentialGraded.compose R (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) g z hk ∈
        dgCoherentBarHomFiltration R D F M k m)
    (fun s : {s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I // s.1 ≤ n} =>
      LinearMap.range ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val)).f p).hom) hf ?_ ?_ ?_
  · intro s f hf
    obtain ⟨a, rfl⟩ := hf
    rw [_root_.SerrePositivity.DifferentialGraded.moduleHomClosedInsertion R D]
    exact dgCoherentBarHomFiltration_compose R D F a _ (hg s.val s.property) hk
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero]
    exact Submodule.zero_mem _
  · intro a b ha hb
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_right]
    exact Submodule.add_mem _ ha hb

lemma dgCoherentBarHomFiltration_postcompose_zero {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} {p q k : ℤ}
    {n : ℕ}
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X p)
    (g : (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X q)
    (hf : f ∈ dgCoherentBarHomFiltration R D F M p n)
    (hg : ∀ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I, s.1 ≤ n →
      (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f q g = 0) (hk : p + q = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) g f hk = 0 := by
  refine Submodule.iSup_induction
    (motive := fun z => _root_.SerrePositivity.DifferentialGraded.compose R (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) g z hk = 0)
    (fun s : {s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I // s.1 ≤ n} =>
      LinearMap.range ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) M
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val)).f p).hom) hf ?_ ?_ ?_
  · intro s f hf
    obtain ⟨a, rfl⟩ := hf
    rw [moduleHomClosedInsertion R D, hg s.val s.property, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose]
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero _ _
  · intro a b ha hb
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_right, ha, hb, add_zero]


lemma dgCoherentBarHomFiltration_postcompose_congr {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} {p q k : ℤ}
    {n : ℕ}
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X p)
    (g h : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X q)
    (hf : f ∈ dgCoherentBarHomFiltration R D F M p n)
    (hgh : ∀ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I, s.1 ≤ n →
      (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f q g =
      (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f q h) (hk : p + q = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) g f hk =
    _root_.SerrePositivity.DifferentialGraded.compose R (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) h f hk := by
  have hz := dgCoherentBarHomFiltration_postcompose_zero R D F f (g - h) hf
    (fun s hs => by rw [map_sub, hgh s hs, sub_self]) hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left] at hz
  exact sub_eq_zero.mp hz

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
