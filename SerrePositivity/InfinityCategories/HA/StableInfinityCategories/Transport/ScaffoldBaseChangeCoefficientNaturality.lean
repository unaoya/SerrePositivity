module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-!
分割で生成：docstring を書き直すこと
 # 元の大域底変換による、同じ切断からの scaffold 復元点の自然性
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport
open _root_.SerrePositivity.KST.Fibration

lemma pointTriangle {C : Type*} [Category C] {a b c d e f g : C}
    (v : a ⟶ b) (l : c ≅ b) (s : c ≅ d) (i : e ≅ d)
    (q : c ≅ f) {j : C} (r : f ≅ j) (z : g ≅ j)
    (x : a ⟶ e) (y : a ⟶ g)
    (hx : v ≫ l.inv ≫ s.hom ≫ i.inv = x)
    (hy : v ≫ l.inv ≫ q.hom ≫ r.hom ≫ z.inv = y) :
    x ≫ (i ≪≫ s.symm ≪≫ q ≪≫ r ≪≫ z.symm).hom = y := by
  rw [← hx]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  exact hy

lemma endpointSpan_heq {C : Type*} [Category C] {a b c d e f : C}
    (h : a = b) (s : c = b) (q : c ≅ d) (r : d = e) (z : f = e) :
    HEq (eqToIso h ≪≫ (eqToIso s).symm ≪≫ q ≪≫ eqToIso r ≪≫ (eqToIso z).symm) q := by
  subst b
  subst c
  subst e
  subst f
  have hs (x : C) : (Iso.refl x).symm = Iso.refl x := rfl
  simp only [eqToIso_refl, hs, Iso.refl_trans, Iso.trans_refl]
  rfl

variable {E B D : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  [Quasicategory B] (k : D ⟶ B) [Quasicategory D]

local instance instLeftFibrationSndSSet_2 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p k) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
