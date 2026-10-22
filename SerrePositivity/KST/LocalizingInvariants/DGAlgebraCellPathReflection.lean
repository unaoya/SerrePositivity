module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathOperations
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMapSurjective
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraIteratedCellResolution

/-!
概要：全射準同型の先にある実乗法的経路を、四重 cell 細分上で元へ反映する。
方針：元の経路を持ち上げ、両端のずれを実相対経路で補正し、実経路を合成する。
規約：準同型局所化後の等式を経路に置き換えない。使われ方：roof 三角形の底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A C B : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)
  {f g : A ⟶ C} (w : Path.Witness R (f ≫ p) (g ≫ p))

/-- 元の経路を各次数全射な経路射を通して持ち上げる。 -/
def cellPathLift : cellResolution R A ⟶ Path.algebra R C :=
  cellResolutionMapLift R w.hom (Path.map R p) (Path.map_surjective R p hs)
    (Path.map_quasiIso R p hq)

lemma cellPathLift_map : cellPathLift R p hs hq w ≫ Path.map R p =
    cellAugmentation R A ≫ w.hom := cellResolutionMapLift_projection R _ _ _ _

lemma cellPathLift_source :
    (cellPathLift R p hs hq w ≫ Path.source R C) ≫ p = cellAugmentation R A ≫ f ≫ p := by
  rw [Category.assoc, ← Path.map_source, ← Category.assoc, cellPathLift_map,
    Category.assoc, w.source_eq]

lemma cellPathLift_target :
    (cellPathLift R p hs hq w ≫ Path.target R C) ≫ p = cellAugmentation R A ≫ g ≫ p := by
  rw [Category.assoc, ← Path.map_target, ← Category.assoc, cellPathLift_map,
    Category.assoc, w.target_eq]

def Path.Witness.cellReflectSurjective : Path.Witness R
    (iteratedCellAugmentation R A 4 ≫ f) (iteratedCellAugmentation R A 4 ≫ g) := by
  let e₀ := cellAugmentation R A
  let e₁ := cellAugmentation R (cellResolution R A)
  let e₂ := cellAugmentation R (cellResolution R (cellResolution R A))
  let t := cellPathLift R p hs hq w
  let a := RelativePath.cellPathWitness R p hs hq (e₀ ≫ f) (t ≫ Path.source R C)
    (cellPathLift_source R p hs hq w).symm
  let b : Path.Witness R (t ≫ Path.source R C) (t ≫ Path.target R C) :=
    { hom := t, source_eq := rfl, target_eq := rfl }
  let c := RelativePath.cellPathWitness R p hs hq (t ≫ Path.target R C) (e₀ ≫ g)
    (cellPathLift_target R p hs hq w)
  let ab := a.cellComp R (b.precomp e₁)
  let abc := ab.cellComp R (c.precomp e₂)
  exact { hom := abc.hom
          source_eq := by
            simpa only [e₀, e₁, e₂, iteratedCellAugmentation, iteratedCellResolution,
              Category.assoc, Category.id_comp, Category.comp_id] using abc.source_eq
          target_eq := by
            simpa only [e₀, e₁, e₂, iteratedCellAugmentation, iteratedCellResolution,
              Category.assoc, Category.id_comp, Category.comp_id] using abc.target_eq }

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
