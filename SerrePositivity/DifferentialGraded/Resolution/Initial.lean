module
public import SerrePositivity.DifferentialGraded.Resolution.CycleCover
public import SerrePositivity.DifferentialGraded.Resolution.Free.Universal

/-! # 全Hom cycleを持ち上げる自由dg圏からの初期増大関手

sourceの全HomはK-flat。増大関手のHomはホモロジー全射であるが、
余分なpath cycleを消すcell付加前なので準同値とはまだ主張しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGCategoryCycleCover
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def edges : FreeDGCategory.ComplexQuiver A D :=
  fun x y => complexCycleCover A (homObject A D x y)

abbrev Source : Type v := FreeDGCategory.Objects A D (edges A D)

/-- 対象はDと同じで、各Homのcycleを生成辺へ持ち上げる増大関手。 -/
def augmentation : DGFunctor A (Source A D) D :=
  FreeDGCategory.lift A D D (edges A D) id
    (fun x y => complexCycleCoverπ A (homObject A D x y))

lemma augmentation_obj (x : D) : (augmentation A D).obj x = x := rfl

lemma source_homKFlat : localHomKFlat A (Source A D) :=
  FreeDGCategory.homKFlat A D (edges A D)
    (fun x y => complexCycleCover_kFlat A (homObject A D x y))

lemma edge_augmentation (x y : D) :
    FreeDGCategory.edgeInclusion A D (edges A D) x y ≫
      (augmentation A D).map x y = complexCycleCoverπ A (homObject A D x y) :=
  FreeDGCategory.lift_edge A D D (edges A D) id _ x y

def sphereLift (x y : D) (n : ℤ) (z : complexCycles A (homObject A D x y) n) :
    complexSphere A n ⟶ homObject A (Source A D) x y :=
  complexCycleCoverLift A (homObject A D x y) n z ≫
    FreeDGCategory.edgeInclusion A D (edges A D) x y

lemma sphereLift_augmentation (x y : D) (n : ℤ)
    (z : complexCycles A (homObject A D x y) n) :
    sphereLift A D x y n z ≫ (augmentation A D).map x y = complexSphereMap A n z := by
  rw [sphereLift, Category.assoc, edge_augmentation]
  exact complexCycleCoverLift_π A (homObject A D x y) n z

lemma cycle_lift (x y : D) (n : ℤ) (z : complexCycles A (homObject A D x y) n) :
    ∃ t : complexCycles A (homObject A (Source A D) x y) n,
      ((augmentation A D).map x y).f n t.val = z.val := by
  refine ⟨complexSphereCycle A n (sphereLift A D x y n z), ?_⟩
  rw [← complexSphereCycle_comp, sphereLift_augmentation]
  exact congrArg Subtype.val
    ((complexSphereHomEquiv A (homObject A D x y) n).apply_symm_apply z)

lemma cyclesMap_epi (x y : D) (n : ℤ) :
    Epi (cyclesMap ((augmentation A D).map x y) n) :=
  complexCyclesMap_epi_of_cycle_lift A _ n (cycle_lift A D x y n)

lemma homologyMap_epi (x y : D) (n : ℤ) :
    Epi (homologyMap ((augmentation A D).map x y) n) :=
  complexHomologyMap_epi_of_cycle_lift A _ n (cycle_lift A D x y n)

/-- 対象写像が恒等なのでH⁰上の本質的全射性は初期段階から成り立つ。 -/
lemma augmentation_essSurj : (augmentation A D).onHomotopy.EssSurj where
  mem_essImage X := by
    let x : Source A D := ForgetEnrichment.to (C := D) (Complex A) X.as
    exact ⟨(toHomotopy A (Source A D)).obj
      (ForgetEnrichment.of (Complex A) x), ⟨Iso.refl _⟩⟩

end SerrePositivity.DifferentialGraded.DGCategoryCycleCover
