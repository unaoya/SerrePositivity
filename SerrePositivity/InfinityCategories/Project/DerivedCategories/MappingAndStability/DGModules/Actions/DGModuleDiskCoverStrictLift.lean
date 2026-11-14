module
public import SerrePositivity.DifferentialGraded.Module.Disk
/-!
概要：canonical 分解の初期自由 disk 被覆から厳密に持ち上げる。
方針：自由 disk の全射評価と余積の実普遍性を使う。
規約：指定比較を変えず、追加の模型圏仮定を置かない。
使われ方：一般 cell 合成の coherence と厳密な模型射。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma dgModuleDiskCover_strict_lift
    (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    (M : ModuleCategory R D) {T N : ModuleCategory R D}
    (q : T ⟶ N) (hq : moduleDegreewiseSurjective R D q)
    (f : moduleDiskCover R D M ⟶ N) :
    ∃ g : moduleDiskCover R D M ⟶ T, g ≫ q = f := by
  have hj : ∀ j : ModuleDiskCoverIndex R D M,
      ∃ g : moduleDiskCoverFamily R D M j ⟶ T,
        g ≫ q = Sigma.ι (moduleDiskCoverFamily R D M) j ≫ f := by
    intro j
    let a := Sigma.ι (moduleDiskCoverFamily R D M) j ≫ f
    obtain ⟨y, hy⟩ := hq j.1 j.2.1 (freeDiskHomEquiv R D j.1 j.2.1 N a)
    refine ⟨(freeDiskHomEquiv R D j.1 j.2.1 T).symm y, ?_⟩
    apply (freeDiskHomEquiv R D j.1 j.2.1 N).injective
    rw [freeDiskHomEquiv_naturality, Equiv.apply_symm_apply]
    exact hy
  choose g hg using hj
  refine ⟨Sigma.desc g, ?_⟩
  apply Sigma.hom_ext
  intro j
  simpa only [← Category.assoc, Sigma.ι_comp_desc] using! hg j
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
