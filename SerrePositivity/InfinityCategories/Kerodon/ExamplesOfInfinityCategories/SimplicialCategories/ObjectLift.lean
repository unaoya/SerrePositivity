module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.SmallKanRealization
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory

/-!
概要：単体的圏の対象宇宙だけを持ち上げ、coherent nerve の持ち上げと照合する。
方針：Hom・単位・合成を元のまま継承する。
規約：対象の持ち上げに際して Hom の宇宙を変更しない。
使われ方：小さい圏の Kan 値関手に、同宇宙の coherent 自然性を適用する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 対象だけを一段持ち上げた単体的圏。 -/
def CoherentObjectLift (D : Type u) := ULift.{u + 1} D

namespace CoherentObjectLift
variable (D : Type u) [Category.{u} D] [SimplicialCategory D]

instance : Category.{u} (CoherentObjectLift D) where
  Hom x y := x.down ⟶ y.down
  id x := 𝟙 x.down
  comp f g := f ≫ g

instance : EnrichedCategory SSet.{u} (CoherentObjectLift D) where
  Hom x y := SimplicialCategory.sHom x.down y.down
  id x := eId SSet x.down
  comp x y z := eComp SSet x.down y.down z.down
  id_comp x y := e_id_comp SSet x.down y.down
  comp_id x y := e_comp_id SSet x.down y.down
  assoc x y z w := e_assoc SSet x.down y.down z.down w.down

instance : SimplicialCategory (CoherentObjectLift D) where
  homEquiv := eHomEquiv SSet (C := D)
  homEquiv_id x := eHomEquiv_id SSet x.down
  homEquiv_comp f g := eHomEquiv_comp SSet (C := D) f g

instance [∀ x y : D, KanComplex (SimplicialCategory.sHom x y)] :
    ∀ x y : CoherentObjectLift D, KanComplex (SimplicialCategory.sHom x y) :=
  fun x y => inferInstanceAs (KanComplex (SimplicialCategory.sHom x.down y.down))

/-- 元の対象を持ち上げる豊穣関手。 -/
def up : EnrichedFunctor SSet.{u} D (CoherentObjectLift D) where
  obj x := ULift.up x
  map _ _ := 𝟙 _

/-- 対象の持ち上げを戻す豊穣関手。 -/
def lower : EnrichedFunctor SSet.{u} (CoherentObjectLift D) D where
  obj x := x.down
  map _ _ := 𝟙 _

/-- 持ち上げた圏の nerve と、元の nerve の単体集合としての持ち上げの同型。 -/
def nerveIso : SimplicialNerve (CoherentObjectLift D) ≅
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialNerve D) where
  hom :=
    { app _ := ↾fun s => ULift.up (s.comp SSet (lower D))
      naturality _ _ _ := rfl }
  inv :=
    { app _ := ↾fun s => s.down.comp SSet (up D)
      naturality _ _ _ := rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply EnrichedFunctor.ext SSet (fun i => by cases s.obj i; rfl)
    intro i j
    simp [up, lower]
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply EnrichedFunctor.ext SSet (fun _ => rfl)
    intro i j
    simp [up, lower]

/-- 同じ元の対象の頂点を、元の nerve の持ち上げた頂点へ戻す。 -/
lemma nerveIso_vertex (x : D) :
    (nerveIso D).hom.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (C := CoherentObjectLift D) (ULift.up x)) =
      ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) := by
  apply ULift.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (C := CoherentObjectLift D) (ULift.up x)).comp SSet (lower D))).symm

/-- Kan 値実現は、対象を持ち上げた圏の通常の coherent 後合成に一致する。 -/
lemma realization (F : EnrichedFunctor SSet.{u} D _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (nerveIso D).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallKanRealization F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap ((lower D).comp SSet F) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply EnrichedFunctor.ext SSet (fun _ => rfl)
  intro i j
  simp only [EnrichedFunctor.comp_map, Category.assoc, eqToHom_refl, Category.comp_id]

end CoherentObjectLift
end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
