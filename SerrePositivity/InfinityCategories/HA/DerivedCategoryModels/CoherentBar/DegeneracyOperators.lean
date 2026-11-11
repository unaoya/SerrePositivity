module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedGraded
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
/-!
概要：元の全単体ラベルの退化写像から、bar 上の次数マイナス一作用素を作る。
方針：始点を保つ退化写像を同じ shift 単位ブロックにし、全 Hom の直積表示で貼り合わせる。
規約：元の theta と全次数の加群作用を保持する。内部微分の閉性と MC 後の縮約は区別する。
使われ方：Dold–Kan の段階的正規化に対応する、実 bar 微分での null homotopy。
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

def dgCoherentBarDegeneracy {n : ℕ} (s : I _⦋n⦌) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I := ⟨n + 1, I.σ i s⟩

lemma dgCoherentBarSource_degeneracy {n : ℕ} (s : I _⦋n⦌) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (dgCoherentBarDegeneracy s i) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩ := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource dgCoherentBarDegeneracy
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex_map F (SimplexCategory.σ i) s 0
  simpa [SimplicialObject.σ, SimplexCategory.σ, Fin.predAboveOrderHom] using h

def dgCoherentBarDegeneracyBlock {n : ℕ} (s : I _⦋n⦌) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s i)))).X (-1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomTargetTransport R D
    (shiftModule (n : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩))
    (shiftModule ((n + 1 : ℕ) : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩))
    (_root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (dgCoherentBarDegeneracy s i)))
    (congrArg (_root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ))
      (dgCoherentBarSource_degeneracy R D F s i).symm) (-1)
    (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D (n : ℤ) ((n + 1 : ℕ) : ℤ)
      (unitElement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)).val (by omega))).val

lemma dgCoherentBarDegeneracyBlock_d {n : ℕ} (s : I _⦋n⦌) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s i)))).d (-1) 0
        (dgCoherentBarDegeneracyBlock R D F s i) = 0 := by
  unfold dgCoherentBarDegeneracyBlock
  change (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
    (shiftModule (n : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩))
    (_root_.SerrePositivity.DifferentialGraded.shiftModule ((n + 1 : ℕ) : ℤ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (dgCoherentBarDegeneracy s i)))).d (-1) 0 _ = 0
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomTargetTransport_d R D]
  erw [_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock_unit_d R D (n : ℤ) ((n + 1 : ℕ) : ℤ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩) (-1) (by omega)]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomTargetTransport_zero R D _ _ _ _ _

def dgCoherentBarDegeneracyColumn {n : ℕ} (s : I _⦋n⦌) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X (-1) :=
  (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩)
    (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (dgCoherentBarDegeneracy s i))).f (-1)
    (dgCoherentBarDegeneracyBlock R D F s i)

def dgCoherentBarNormalizationHomotopyColumn (q : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X (-1) :=
  if s.1 < q then 0 else
    ((q : ℤ) + 1).negOnePow •
      dgCoherentBarDegeneracyColumn R D F s.2 ⟨s.1 - q, by omega⟩

def dgCoherentBarNormalizationHomotopyGraded (q : ℕ) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).X (-1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) (-1)).symm
    (dgCoherentBarNormalizationHomotopyColumn R D F q)

lemma dgCoherentBarNormalizationHomotopyColumn_eq_zero_of_lt (q : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) (hs : s.1 < q) :
    dgCoherentBarNormalizationHomotopyColumn R D F q s = 0 := by
  simp only [dgCoherentBarNormalizationHomotopyColumn, ite_eq_left hs]

lemma dgCoherentBarDegeneracyColumn_d {n : ℕ} (s : I _⦋n⦌) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d (-1) 0
        (dgCoherentBarDegeneracyColumn R D F s i) = 0 := by
  have h := ConcreteCategory.congr_hom
    ((eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩)
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (dgCoherentBarDegeneracy s i))).comm (-1) 0)
        (dgCoherentBarDegeneracyBlock R D F s i)
  symm at h
  change (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩)
    (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) (dgCoherentBarDegeneracy s i))).f 0
      ((_root_.SerrePositivity.DifferentialGraded.moduleHom R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s i)))).d (-1) 0
            (dgCoherentBarDegeneracyBlock R D F s i)) = (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d (-1) 0
      (dgCoherentBarDegeneracyColumn R D F s i) at h
  rw [dgCoherentBarDegeneracyBlock_d, map_zero] at h
  exact h.symm

lemma dgCoherentBarNormalizationHomotopyColumn_d (q : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d (-1) 0
        (dgCoherentBarNormalizationHomotopyColumn R D F q s) = 0 := by
  rcases s with ⟨n, s⟩
  unfold dgCoherentBarNormalizationHomotopyColumn
  split_ifs
  · exact map_zero _
  · simp only [Units.smul_def, map_zsmul, dgCoherentBarDegeneracyColumn_d, smul_zero]

lemma dgCoherentBarNormalizationHomotopyGraded_restrict (q : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f (-1)
      (dgCoherentBarNormalizationHomotopyGraded R D F q) =
    dgCoherentBarNormalizationHomotopyColumn R D F q s := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv_apply]
  exact congrFun (LinearEquiv.apply_symm_apply
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) (-1)) _) s

lemma dgCoherentBarNormalizationHomotopyGraded_d (q : ℕ) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d (-1) 0
        (dgCoherentBarNormalizationHomotopyGraded R D F q) = 0 := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) 0).injective
  funext s
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv_apply]
  have h := ConcreteCategory.congr_hom
    ((eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).comm (-1) 0)
        (dgCoherentBarNormalizationHomotopyGraded R D F q)
  symm at h
  change (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0
      ((_root_.SerrePositivity.DifferentialGraded.moduleHom R D
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d (-1) 0
          (dgCoherentBarNormalizationHomotopyGraded R D F q)) = (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s))
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d (-1) 0
      ((eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f (-1)
          (dgCoherentBarNormalizationHomotopyGraded R D F q)) at h
  rw [h, dgCoherentBarNormalizationHomotopyGraded_restrict,
    dgCoherentBarNormalizationHomotopyColumn_d]
  simp only [map_zero, Pi.zero_apply]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
