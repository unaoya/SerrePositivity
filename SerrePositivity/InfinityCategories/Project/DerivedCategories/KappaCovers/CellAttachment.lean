module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.SubsetModule
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.ConeEmbedding
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

/-!
概要：選択した kernel cell の境界を、単射な小さい前段へ持ち上げて付加する。
方針：斉次境界の持上げの cycle 条件を単射性で反映し、自由 sphere の普遍性を使う。
規約：境界の持上げ可能性はこの局所補題の引数であり、全体の存在定理ではない。
使われ方：D-8 d の依存閉部分集合からの実 cell 構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

def dgKappaCycleLift {P M : ModuleCategory R D} (i : P ⟶ M)
    (hm : ∀ x n, Mono (((moduleEvaluation R D x).map i).f n)) (x : D) (n : ℤ)
    (z : complexCycles R ((moduleEvaluation R D x).obj M) n)
    (hz : ∃ a, ((moduleEvaluation R D x).map i).f n a = z.val) :
    complexCycles R ((moduleEvaluation R D x).obj P) n := by
  refine ⟨hz.choose, ?_⟩
  have hi := (ModuleCat.mono_iff_injective _).mp (hm x (n + 1))
  apply hi
  have hc := congrArg (fun k => k hz.choose)
    (((moduleEvaluation R D x).map i).comm n (n + 1))
  have hz0 : ((moduleEvaluation R D x).obj M).d n (n + 1) z.val = 0 := z.property
  simpa only [ModuleCat.comp_apply, hz.choose_spec, hz0, map_zero] using! hc.symm

lemma dgKappaCycleLift_val {P M : ModuleCategory R D} (i : P ⟶ M)
    (hm : ∀ x n, Mono (((moduleEvaluation R D x).map i).f n)) (x : D) (n : ℤ)
    (z : complexCycles R ((moduleEvaluation R D x).obj M) n)
    (hz : ∃ a, ((moduleEvaluation R D x).map i).f n a = z.val) :
    ((moduleEvaluation R D x).map i).f n (dgKappaCycleLift R D i hm x n z hz).val = z.val :=
  hz.choose_spec

variable {M N P : ModuleCategory R D} (f : M ⟶ N)
  (s : Set (ModuleKernelCellIndex R D f)) (i : P ⟶ M)
  (hm : ∀ x n, Mono (((moduleEvaluation R D x).map i).f n))
  (hl : ∀ j : s, ∃ a,
    ((moduleEvaluation R D j.val.1).map i).f (j.val.2.1 + 1) a = j.val.2.2.val.val)

def dgKappaKernelSubsetAttachment :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModule R D (moduleKernelCellFamily R D f) s ⟶ P :=
  Sigma.desc (fun j : s => (freeSphereHomEquiv R D j.val.1 (j.val.2.1 + 1) P).symm
    (dgKappaCycleLift R D i hm j.val.1 (j.val.2.1 + 1) j.val.2.2.val (hl j)))

@[reassoc] lemma dgKappaKernelSubsetAttachment_ι (j : s) :
    Sigma.ι (fun j : s => moduleKernelCellFamily R D f j.val) j ≫
      dgKappaKernelSubsetAttachment R D f s i hm hl =
        (freeSphereHomEquiv R D j.val.1 (j.val.2.1 + 1) P).symm
          (dgKappaCycleLift R D i hm j.val.1 (j.val.2.1 + 1) j.val.2.2.val (hl j)) :=
  Sigma.ι_comp_desc _ _

-- The selected module Hom limits require more unfolding in the free-sphere comparison.
set_option maxHeartbeats 300000 in
lemma dgKappaKernelSubsetAttachment_square :
    dgKappaKernelSubsetAttachment R D f s i hm hl ≫ i =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleInclusion R D (moduleKernelCellFamily R D f) s ≫
        moduleKernelCellMap R D f := by
  apply Sigma.hom_ext
  intro j
  calc
    _ = (freeSphereHomEquiv R D j.val.1 (j.val.2.1 + 1) P).symm
        (dgKappaCycleLift R D i hm j.val.1 (j.val.2.1 + 1) j.val.2.2.val (hl j)) ≫ i :=
      dgKappaKernelSubsetAttachment_ι_assoc R D f s i hm hl j i
    _ = (freeSphereHomEquiv R D j.val.1 (j.val.2.1 + 1) M).symm j.val.2.2.val := by
      apply (freeSphereHomEquiv R D j.val.1 (j.val.2.1 + 1) M).injective
      apply Subtype.ext
      let z := dgKappaCycleLift R D i hm j.val.1 (j.val.2.1 + 1) j.val.2.2.val (hl j)
      let g := (freeSphereHomEquiv R D j.val.1 (j.val.2.1 + 1) P).symm z
      have hn := freeSphereHomEquiv_naturality_val R D j.val.1 (j.val.2.1 + 1) g i
      have he := congrArg (fun c => ((moduleEvaluation R D j.val.1).map i).f
          (j.val.2.1 + 1) c.val)
        ((freeSphereHomEquiv R D j.val.1 (j.val.2.1 + 1) P).apply_symm_apply z)
      have hr := congrArg Subtype.val
        ((freeSphereHomEquiv R D j.val.1 (j.val.2.1 + 1) M).apply_symm_apply j.val.2.2.val)
      exact (hn.trans (he.trans (dgKappaCycleLift_val R D i hm _ _ _ (hl j)))).trans hr.symm
    _ = _ := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleInclusion_ι_assoc R D
      (moduleKernelCellFamily R D f) s j (moduleKernelCellMap R D f)).trans
        (moduleKernelCellι_map R D f j.val)).symm

def dgKappaKernelSubsetStepInclusion :
    moduleCone R D (dgKappaKernelSubsetAttachment R D f s i hm hl) ⟶
      moduleKernelCellStep R D f :=
  moduleConeMap R D _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleInclusion R D (moduleKernelCellFamily R D f) s)
    i (dgKappaKernelSubsetAttachment_square R D f s i hm hl)

lemma dgKappaKernelSubsetStepInclusion_degreewiseMono (x : D) (n : ℤ) :
    Mono (((moduleEvaluation R D x).map
      (dgKappaKernelSubsetStepInclusion R D f s i hm hl)).f n) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaModuleConeMap_degreewiseMono R D _ _ _ _ _ x n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModuleInclusion_degreewiseMono R D _ s x (n + 1)) (hm x n)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
