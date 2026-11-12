module

public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.EnrichedClosedWhiskering

/-!
概要：右 dg 加群の実可算直和の全 Hom chain map。
方針：全 Hom end の余積普遍性で、各注入への後合成を同時に延長する。
規約：閉零射だけの作用に置き換えず、全次数と微分を保持する。
使われ方：κ-compact dg cone 上に制限する可算直和関手と swindle。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 元の実 dg 加群の可算定値族の、実際の直和。 -/
abbrev dgCountableSumObj (M : ModuleCategory R D) : ModuleCategory R D :=
  ∐ (fun _ : ℕ ↦ M)

/-- 元の直和の各成分への、閉零の標準注入。 -/
abbrev dgCountableSumInjection (M : ModuleCategory R D) (n : ℕ) :
    M ⟶ dgCountableSumObj R D M := Sigma.ι (fun _ : ℕ ↦ M) n

/-- 全 Hom 複体の実普遍性で構成した、可算直和上の同じ chain map。 -/
def dgCountableSumHom (M N : ModuleCategory R D) :
    (M ⟶[Complex R] N) ⟶ (dgCountableSumObj R D M ⟶[Complex R] dgCountableSumObj R D N) :=
  moduleCoproductHomLift R D (fun _ : ℕ ↦ M) (dgCountableSumObj R D N)
    (Fan.mk (M ⟶[Complex R] N)
      (fun n ↦ eHomWhiskerLeft (Complex R) M (dgCountableSumInjection R D N n)))

/-- 全次数の作用は、元の各標準注入の前後合成と厳密に可換。 -/
@[reassoc] lemma dgCountableSumHom_injection (M N : ModuleCategory R D) (n : ℕ) :
    dgCountableSumHom R D M N ≫
      eHomWhiskerRight (Complex R) (dgCountableSumInjection R D M n)
        (dgCountableSumObj R D N) =
      eHomWhiskerLeft (Complex R) M (dgCountableSumInjection R D N n) :=
  moduleCoproductHomLift_π R D _ _ _ n

/-- 可算直和上の全 Hom 作用は、元の閉単位を保存する。 -/
lemma dgCountableSumHom_id (M : ModuleCategory R D) :
    eId (Complex R) M ≫ dgCountableSumHom R D M M =
      eId (Complex R) (dgCountableSumObj R D M) := by
  apply (moduleCoproductHomIsLimit R D (fun _ : ℕ ↦ M) (dgCountableSumObj R D M)).hom_ext
  intro n
  change (eId (Complex R) M ≫ dgCountableSumHom R D M M) ≫
      eHomWhiskerRight (Complex R) (dgCountableSumInjection R D M n.as) _ = _
  rw [Category.assoc, dgCountableSumHom_injection]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedIdentity_postcompose (Complex R) (ModuleCategory R D) _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedIdentity_precompose (Complex R) (ModuleCategory R D) _).symm

/-- 可算直和は射影的 dg 加群を射影的 dg 加群へ送る。 -/
lemma dgCountableSumObj_projective (M : ModuleCategory R D)
    (hM : moduleHomotopicallyProjective R D M) :
    moduleHomotopicallyProjective R D (dgCountableSumObj R D M) :=
  moduleCoproduct_homotopicallyProjective R D _ (fun _ ↦ hM)

/-- 可算直和上の全 Hom 作用は、元の豊穣合成を全次数で保存する。 -/
lemma dgCountableSumHom_comp (M N P : ModuleCategory R D) :
    eComp (Complex R) M N P ≫ dgCountableSumHom R D M P =
      (dgCountableSumHom R D M N ⊗ₘ dgCountableSumHom R D N P) ≫
        eComp (Complex R) (dgCountableSumObj R D M) (dgCountableSumObj R D N)
          (dgCountableSumObj R D P) := by
  apply (moduleCoproductHomIsLimit R D (fun _ : ℕ ↦ M) (dgCountableSumObj R D P)).hom_ext
  intro n
  change (eComp (Complex R) M N P ≫ dgCountableSumHom R D M P) ≫
    eHomWhiskerRight (Complex R) (dgCountableSumInjection R D M n.as) _ =
      ((dgCountableSumHom R D M N ⊗ₘ dgCountableSumHom R D N P) ≫
        eComp (Complex R) (dgCountableSumObj R D M) (dgCountableSumObj R D N)
          (dgCountableSumObj R D P)) ≫
        eHomWhiskerRight (Complex R) (dgCountableSumInjection R D M n.as) _
  rw [Category.assoc, dgCountableSumHom_injection, eComp_eHomWhiskerLeft]
  symm
  rw [Category.assoc, eComp_eHomWhiskerRight, tensorHom_def', Category.assoc,
    ← comp_whiskerRight_assoc, dgCountableSumHom_injection]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedComposition_middle]
  rw [← whiskerLeft_comp_assoc, dgCountableSumHom_injection]

/-- 元の実可算直和は、全 Hom chain map を持つ厳密 dg 自己関手。 -/
def dgCountableSumFunctor : DGFunctor R (ModuleCategory R D) (ModuleCategory R D) where
  obj := dgCountableSumObj R D
  map := dgCountableSumHom R D
  map_id := dgCountableSumHom_id R D
  map_comp := dgCountableSumHom_comp R D

end SerrePositivity.KST.NonConnective
