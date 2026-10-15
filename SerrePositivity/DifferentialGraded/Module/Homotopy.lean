module
public import SerrePositivity.DifferentialGraded.Module.Category
public import SerrePositivity.DifferentialGraded.Category.Comparison
public import Mathlib.Algebra.Homology.HomotopyCategory

/-! # 全次数 Hom end の境界による加群ホモトピーと K(D)

次数 −1 の要素を Hom end 内に取るため、全 dg 作用との自然性も要求する。
対象ごとに独立した chain homotopy の存在だけでは代用しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 dg 自然な次数 −1 の要素で、その微分が閉零射の差となるもの。 -/
def ModuleHomotopy {M N : ModuleCategory A D} (f g : M ⟶ N) :=
  { h : (homObject A (RightModule A D) M N).X (-1) //
    (homObject A (RightModule A D) M N).d (-1) 0 h =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val -
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) g)).val }

lemma moduleHomotopy_nonempty_iff {M N : ModuleCategory A D} (f g : M ⟶ N) :
    Nonempty (ModuleHomotopy A D f g) ↔ boundaryRelation A (RightModule A D) f g := by
  rw [boundaryRelation, unit_homotopy_boundary]
  exact ⟨fun ⟨h⟩ => ⟨h.val, h.property⟩, fun ⟨h, dh⟩ => ⟨⟨h, dh⟩⟩⟩

/-- K(D) は主加群 dg 圏の H⁰、すなわち全 dg 自然な境界による商。 -/
abbrev ModuleHomotopyCategory := HomotopyCategory A (RightModule A D)

/-- 閉零加群圏から K(D) への A 線形な商関手。 -/
abbrev moduleToHomotopy : ModuleCategory A D ⥤ ModuleHomotopyCategory A D :=
  toHomotopy A (RightModule A D)

lemma moduleToHomotopy_map_eq_iff {M N : ModuleCategory A D} (f g : M ⟶ N) :
    (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g ↔
      Nonempty (ModuleHomotopy A D f g) := by
  rw [toHomotopy_map_eq_iff, moduleHomotopy_nonempty_iff]

/-- 加群ホモトピーは、すべての評価で既存 chain homotopy を与える。 -/
lemma moduleHomotopy_evaluation {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) (x : D) :
    Nonempty (Homotopy ((moduleEvaluation A D x).map f)
      ((moduleEvaluation A D x).map g)) := by
  have hb := (moduleHomotopy_nonempty_iff A D f g).1 ⟨h⟩
  have he := (moduleEvaluationDG A D x).preserves_boundary f g hb
  exact (complex_boundary_iff A _ _ _ _).1 he

/-- K(D) の評価を既存の複体ホモトピー圏へ降ろす。 -/
def moduleHomotopyEvaluation (x : D) : ModuleHomotopyCategory A D ⥤
    _root_.HomotopyCategory (ModuleCat A) (.up ℤ) :=
  CategoryTheory.Quotient.lift _ (moduleEvaluation A D x ⋙
    _root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ)) (by
      intro M N f g hb
      obtain ⟨h⟩ := (moduleHomotopy_nonempty_iff A D f g).2 hb
      obtain ⟨he⟩ := moduleHomotopy_evaluation A D h x
      exact _root_.HomotopyCategory.eq_of_homotopy _ _ he)

lemma moduleHomotopyEvaluation_fac (x : D) :
    moduleToHomotopy A D ⋙ moduleHomotopyEvaluation A D x =
      moduleEvaluation A D x ⋙ _root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ) :=
  CategoryTheory.Quotient.lift_spec _ _ _

end SerrePositivity.DifferentialGraded
