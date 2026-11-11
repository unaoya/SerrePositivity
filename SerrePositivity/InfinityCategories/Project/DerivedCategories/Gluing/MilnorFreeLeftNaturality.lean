module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorFreeHomComponents
public import SerrePositivity.KST.SConstruction.DGPerfectRealization
/-!
概要：元の左辺の代表延長同型は自由対象の全 Hom に関して自然である。
方針：perfect 値の代表評価の公開自然性を同じ graph へ適用する。
規約：元の延長と代表同型を保持し、比較を選び直さない。
使われ方：実自由対角の左 Hom 成分を元代数射へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top
lemma dgGluingMilnorLeftRepresentable_naturality (x y : A) :
    yonedaHom R (A) x y ≫ (dgModuleExtension R (A) (C) (L)).map
      (representable R x) (representable R y) ≫
      moduleHomPostcompose R (C) _ _ _ (dgModuleExtensionRepresentableIso R (A) (C) (L) y).hom =
    ((L).map x y ≫ yonedaHom R (C) ((L).obj x) ((L).obj y)) ≫
      moduleHomPrecompose R (C) _ _ _
        (dgModuleExtensionRepresentableIso R (A) (C) (L) x).hom := by
  let K : DGFunctor R (A) (PerfectDGModule R (C)) :=
    { obj := fun a => dgRepresentablePerfectPoint R (C) ((L).obj a)
      map := fun a b => (L).map a b ≫ yonedaHom R (C) ((L).obj a) ((L).obj b)
      map_id := fun a => ((L).comp (dgYoneda R (C))).map_id a
      map_comp := fun a b c => ((L).comp (dgYoneda R (C))).map_comp a b c }
  have hk : dgPerfectRealizationKernel R (A) (C) K = functorGraph R (A) (C) (L) := by
    apply EnrichedFunctor.ext (Complex R)
    case h_obj => intro a; rfl
    intro a b
    simp only [eqToHom_refl, Category.comp_id]
    change ((L).map a b ≫ yonedaHom R (C) ((L).obj a) ((L).obj b)) ≫ 𝟙 _ = _
    exact Category.comp_id _
  have h := dgPerfectRealizationRepresentableIso_naturality R (A) (C) K x y
  let T (P : Bimodule R (C) (A)) : Prop :=
    yonedaHom R (A) x y ≫
      (BimoduleTensor.compose R (C) (A) (RightModule R (A)) P
        (DGFunctor.id _)).toFunctor.map (representable R x) (representable R y) ≫
      moduleHomPostcompose R (C) _ _ (P.obj y)
        (BimoduleTensor.rightUnitIso R (C) (A) P y).hom =
    P.map x y ≫ moduleHomPrecompose R (C) _ _ _
      (BimoduleTensor.rightUnitIso R (C) (A) P x).hom
  have ht : T (dgPerfectRealizationKernel R (A) (C) K) := h
  have ht' : T (functorGraph R (A) (C) (L)) := hk ▸ ht
  exact ht'
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
