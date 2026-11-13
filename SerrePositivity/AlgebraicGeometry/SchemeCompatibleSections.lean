module

public import SerrePositivity.AlgebraicGeometry.SchemeSectionAlgebraCech
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
概要：一般の開被覆の適合する構造層の切断を、大域切断の環と比較する。
方針：層の一意な貼り合わせを実際の制限環準同型に適用する。
規約：全空間のアフィン性や被覆の非空性は仮定しない。
使われ方：F7 の Čech H⁰ の環から大域切断と Spec の全射性へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable (Y : Scheme.{u}) {ι : Type} (U : ι → Y.Opens)

/-- 二重点で一致する切断族の部分環。乗法は構造層の切断の乗法。 -/
def schemeCompatibleSections : Subring ((i : ι) → Γ(Y, U i)) where
  carrier := {s | TopCat.Presheaf.IsCompatible Y.presheaf U s}
  zero_mem' := by intro i j; simp only [Pi.zero_apply, map_zero]
  one_mem' := by intro i j; simp only [Pi.one_apply, map_one]
  add_mem' ha hb := by
    intro i j
    simp only [Pi.add_apply, map_add, ha i j, hb i j]
  neg_mem' ha := by
    intro i j
    simp only [Pi.neg_apply, map_neg, ha i j]
  mul_mem' ha hb := by
    intro i j
    simp only [Pi.mul_apply, map_mul, ha i j, hb i j]

/-- 大域切断を各開集合へ制限する環準同型。 -/
def schemeGlobalToCompatibleSections : Γ(Y, ⊤) →+* schemeCompatibleSections Y U where
  toFun s := ⟨fun i ↦ (Y.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op).hom s, by
    intro i j
    change (Y.presheaf.map _).hom ((Y.presheaf.map _).hom s) =
      (Y.presheaf.map _).hom ((Y.presheaf.map _).hom s)
    change (Y.presheaf.map _ ≫ Y.presheaf.map _).hom s =
      (Y.presheaf.map _ ≫ Y.presheaf.map _).hom s
    rw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
    congr 2⟩
  map_zero' := by apply Subtype.ext; funext i; exact map_zero _
  map_one' := by apply Subtype.ext; funext i; exact map_one _
  map_add' s t := by apply Subtype.ext; funext i; exact map_add _ s t
  map_mul' s t := by apply Subtype.ext; funext i; exact map_mul _ s t

/-- 実際の制限準同型の各成分は、構造層の制限そのもの。 -/
theorem schemeGlobalToCompatibleSections_apply (s : Γ(Y, ⊤)) (i : ι) :
    (schemeGlobalToCompatibleSections Y U s).val i =
      (Y.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op).hom s := rfl

variable (hcover : (⨆ i, U i) = ⊤)

include hcover in
/-- 被覆上の適合する切断は、大域切断から一意に得られる。 -/
theorem schemeGlobalToCompatibleSections_bijective :
    Function.Bijective (schemeGlobalToCompatibleSections Y U) := by
  constructor
  · intro s t h
    apply TopCat.Sheaf.eq_of_locally_eq' Y.sheaf U ⊤
      (fun i ↦ homOfLE (show U i ≤ ⊤ from le_top)) (by rw [hcover])
    intro i
    exact congrArg (fun a ↦ a.val i) h
  · intro a
    obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf U ⊤
      (fun i ↦ homOfLE (show U i ≤ ⊤ from le_top)) (by rw [hcover]) a.val a.property
    exact ⟨s, Subtype.ext (funext hs)⟩

/-- 一般の開被覆の適合する切断の環と大域切断の環の同型。 -/
def schemeGlobalCompatibleSectionsEquiv : Γ(Y, ⊤) ≃+* schemeCompatibleSections Y U :=
  RingEquiv.ofBijective (schemeGlobalToCompatibleSections Y U)
    (schemeGlobalToCompatibleSections_bijective Y U hcover)

end SerrePositivity.AlgebraicGeometry
