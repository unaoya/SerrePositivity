module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SkeletalDimension
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanPushoutCube
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedCoproducts
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Natural comparisons of cocontinuous mono-preserving functors are detected on simplices

The proof uses the actual boundary cell pushouts and the actual skeletal
colimit. It does not assume that the localization preserves colimits.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.CellularNaturalComparison
variable {U V : SSet.{v} ⥤ SSet.{v}} (η : U ⟶ V)

include η in
lemma of_iso {X Y : SSet.{v}} (e : X ≅ Y)
    (hX : IsIso (AnodyneHomotopy.anodyneQ.map (η.app X))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (η.app Y)) := by
  have h := congrArg AnodyneHomotopy.anodyneQ.map (η.naturality e.hom)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  have : IsIso (AnodyneHomotopy.anodyneQ.map (η.app X)) := hX
  have : IsIso (AnodyneHomotopy.anodyneQ.map (U.map e.hom) ≫
      AnodyneHomotopy.anodyneQ.map (η.app Y)) := h.symm ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp this

variable [PreservesColimitsOfSize.{v, v} U] [PreservesColimitsOfSize.{v, v} V]

local instance : PreservesColimitsOfSize.{0, 0} U :=
  preservesSmallestColimits_of_preservesColimits U
local instance : PreservesColimitsOfSize.{0, 0} V :=
  preservesSmallestColimits_of_preservesColimits V

lemma initial_isIso : IsIso (AnodyneHomotopy.anodyneQ.map (η.app (⊥_ SSet.{v}))) := by
  have : IsIso (η.app (⊥_ SSet.{v})) :=
    isIso_of_isInitial (initialIsInitial.isInitialObj U)
      (initialIsInitial.isInitialObj V) _
  infer_instance

lemma coproduct_isIso {I : Type v} (X : I → SSet.{v})
    (hX : ∀ i, IsIso (AnodyneHomotopy.anodyneQ.map (η.app (X i)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (η.app (∐ X))) :=
  KanLocalizedCoproducts.actual_localized_isIso I (fun i => η.app (X i)) hX
    (Cofan.mk _ (fun i => U.map (Limits.Sigma.ι X i)))
    (Cofan.mk _ (fun i => V.map (Limits.Sigma.ι X i)))
    (isColimitCofanMkObjOfIsColimit U X _ (coproductIsCoproduct X))
    (isColimitCofanMkObjOfIsColimit V X _ (coproductIsCoproduct X))
    (η.app _) (fun _ => η.naturality _)

variable [U.PreservesMonomorphisms] [V.PreservesMonomorphisms]

lemma pushout_isIso {A B C P : SSet.{v}} (i : A ⟶ B) [Mono i]
    (j : A ⟶ C) (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout i j u g)
    (hA : IsIso (AnodyneHomotopy.anodyneQ.map (η.app A)))
    (hB : IsIso (AnodyneHomotopy.anodyneQ.map (η.app B)))
    (hC : IsIso (AnodyneHomotopy.anodyneQ.map (η.app C))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (η.app P)) :=
  KanPushoutCube.localized_isIso (U.map i) (U.map j) (U.map u) (U.map g) (sq.map U)
    (V.map i) (V.map j) (V.map u) (V.map g) (sq.map V)
    (η.app A) (η.app B) (η.app C) (η.app P)
    (η.naturality i) (η.naturality j) (η.naturality u) (η.naturality g) hA hB hC

abbrev cellMap (X : SSet.{v}) := initial.to X
abbrev stage (X : SSet.{v}) (n : ℕ) := (SSet.skeletonOfMono (cellMap X) n).toSSet

variable (hstd : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map
  (η.app (SSet.stdSimplex.obj (SimplexCategory.mk n)))))

include hstd in
lemma stage_isIso : ∀ n (X : SSet.{v}), IsIso (AnodyneHomotopy.anodyneQ.map (η.app (stage X n)))
  | 0, X => of_iso η (SSet.relativeCellComplexOfMono (cellMap X)).isoBot.symm (initial_isIso η)
  | n + 1, X => by
    have hb : IsIso (AnodyneHomotopy.anodyneQ.map (η.app (SSet.boundary.{v} n).toSSet)) :=
      of_iso η (SkeletalDimension.stageIso (cellMap (SSet.boundary.{v} n).toSSet) n)
        (stage_isIso n _)
    let i := cellMap X
    have hB : IsIso (AnodyneHomotopy.anodyneQ.map
        (η.app (SSet.relativeCellComplexOfMono.sigmaBoundary i n))) :=
      coproduct_isIso η _ (fun _ => hb)
    have hS : IsIso (AnodyneHomotopy.anodyneQ.map
        (η.app (SSet.relativeCellComplexOfMono.sigmaStdSimplex i n))) :=
      coproduct_isIso η _ (fun _ => hstd n)
    exact pushout_isIso η (SSet.relativeCellComplexOfMono.l i n)
      (SSet.relativeCellComplexOfMono.t i n) (SSet.relativeCellComplexOfMono.b i n)
      (SSet.relativeCellComplexOfMono.r i n) (SSet.relativeCellComplexOfMono.isPushout i n).flip
      hB hS (stage_isIso n X)

include hstd in
lemma app_isIso (X : SSet.{v}) : IsIso (AnodyneHomotopy.anodyneQ.map (η.app X)) := by
  let d := SSet.relativeCellComplexOfMono (cellMap X)
  let α := Functor.whiskerLeft d.F η
  have hs : ∀ n, Mono ((d.F ⋙ U).map (homOfLE (Nat.le_succ n))) := by
    intro n
    change Mono (U.map (SSet.relativeCellComplexOfMono.r (cellMap X) n))
    infer_instance
  have hα : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (α.app n)) :=
    fun n => stage_isIso η hstd n X
  exact KanSequentialColimitComparison.actual_localized_isIso α hs hα
    (U.mapCocone (Cocone.mk X d.incl)) (V.mapCocone (Cocone.mk X d.incl))
    (isColimitOfPreserves U d.isColimit) (isColimitOfPreserves V d.isColimit)
    (η.app X) (fun n => η.naturality _)

end SerrePositivity.SimplicialModel.CellularNaturalComparison
