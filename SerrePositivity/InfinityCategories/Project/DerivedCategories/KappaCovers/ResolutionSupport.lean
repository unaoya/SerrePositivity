module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.ResolutionLabels
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-!
概要：標準 resolution の各有限段の斉次要素に、有限のセル support を与える。
方針：自由 disk の有限 support と、cone の二成分分解を次数ごとに帰納する。
規約：support は一意ではなく、任意の選択が依存閉包に使える。
使われ方：D-8 d の kernel cell の境界依存先。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded CochainComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : ModuleCategory R D)

def DGKappaResolutionElementSupported (s : Set (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaResolutionLabel R D M)) :
    (n : ℕ) → (x : D) → (q : ℤ) →
      ((moduleEvaluation R D x).obj (moduleResolutionStage R D M n).left).X q → Prop
  | 0, x, q, z => ∃ b : ((moduleEvaluation R D x).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModule R D (moduleDiskCoverFamily R D M)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDiskSelection R D M s))).X q,
      ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleInclusion R D
        (moduleDiskCoverFamily R D M) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDiskSelection R D M s))).f q b = z
  | n + 1, x, q, z =>
    ∃ (a : ((moduleEvaluation R D x).obj (moduleResolutionStage R D M n).left).X q)
      (b : ((moduleEvaluation R D x).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModule R D
          (moduleKernelCellFamily R D (moduleResolutionStage R D M n).hom)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M s n))).X (q + 1)),
      DGKappaResolutionElementSupported s n x q a ∧
      (mappingCone.inr ((moduleEvaluation R D x).map
        (moduleKernelCellMap R D (moduleResolutionStage R D M n).hom))).f q a +
      (mappingCone.inl ((moduleEvaluation R D x).map
        (moduleKernelCellMap R D (moduleResolutionStage R D M n).hom))).v (q + 1) q
          (by omega)
        (((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleInclusion R D
          (moduleKernelCellFamily R D (moduleResolutionStage R D M n).hom)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelSelection R D M s n))).f (q + 1) b) = z

lemma dgKappaResolutionElement_finiteSupport (n : ℕ) (x : D) (q : ℤ)
    (z : ((moduleEvaluation R D x).obj (moduleResolutionStage R D M n).left).X q) :
    ∃ t : Finset (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaResolutionLabel R D M),
      ∀ s : Set (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaResolutionLabel R D M), (↑t : Set _) ⊆ s →
        DGKappaResolutionElementSupported R D M s n x q z := by
  classical
  induction n with
  | zero =>
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModule_finiteLabelElement R D (moduleDiskCoverFamily R D M)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionDiskLabel R D M) x q z
  | succ n ih =>
    let f := (moduleEvaluation R D x).map
      (moduleKernelCellMap R D (moduleResolutionStage R D M n).hom)
    let a := (mappingCone.snd f).v q q (add_zero q) z
    let b := (mappingCone.fst f).val.v q (q + 1) rfl z
    obtain ⟨ta, hta⟩ := ih a
    obtain ⟨tb, htb⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModule_finiteLabelElement R D
      (moduleKernelCellFamily R D (moduleResolutionStage R D M n).hom)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionKernelLabel R D M n) x (q + 1) b
    refine ⟨ta ∪ tb, fun s hs => ?_⟩
    obtain ⟨b', hb'⟩ := htb s (fun _ h => hs (Finset.mem_union_right _ h))
    refine ⟨a, b', hta s (fun _ h => hs (Finset.mem_union_left _ h)), ?_⟩
    have he := congrArg (fun w => (mappingCone.inr f).f q a +
      (mappingCone.inl f).v (q + 1) q (by omega) w) hb'
    have h := congrArg (fun k => k z) (mappingCone.id_X f q (q + 1) rfl)
    have hz : (mappingCone.inr f).f q a +
        (mappingCone.inl f).v (q + 1) q (by omega) b = z := by
      simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply, ModuleCat.id_apply,
        a, b, add_comm] using! h
    exact he.trans hz

def dgKappaResolutionElementSupport (n : ℕ) (x : D) (q : ℤ)
    (z : ((moduleEvaluation R D x).obj (moduleResolutionStage R D M n).left).X q) :
    Finset (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaResolutionLabel R D M) :=
  (dgKappaResolutionElement_finiteSupport R D M n x q z).choose

lemma dgKappaResolutionElementSupport_spec (n : ℕ) (x : D) (q : ℤ)
    (z : ((moduleEvaluation R D x).obj (moduleResolutionStage R D M n).left).X q)
    {s : Set (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaResolutionLabel R D M)}
    (hs : (↑(dgKappaResolutionElementSupport R D M n x q z) : Set _) ⊆ s) :
    DGKappaResolutionElementSupported R D M s n x q z :=
  (dgKappaResolutionElement_finiteSupport R D M n x q z).choose_spec s hs

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
