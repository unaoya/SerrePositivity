module

public import SerrePositivity.HomologicalAlgebra.SequentialComplexColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # 複体の完全な余極限とホモロジー

## 概要

任意の形の完全な余極限が chain ホモロジーと可換すること（`chainHomology_preservesExactColimits`）、係数関手の各点の余極限が完全性・加法性・線形性を保つことを示す。

## 方針

ホモロジーを短複体の完全性で書き、完全な余極限が有限の極限・余極限と可換することを使う。

## 規約

列の余極限の場合は SequentialComplexColimits（BS が import するので別ファイルのまま）。exact colimit とホモロジーの可換は Mathlib への提出候補。

## 使われ方

局所コホモロジーの余極限の表示、導来完備化。
-/

@[expose] public noncomputable section

universe v u w t v₁ v₂ v₃ u₁ u₂ u₃

section ExactChainHomologyColimitsPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {J : Type w} [Category.{t} J]

/-- Transpose a chain diagram into a chain complex of diagrams. -/
def chainDiagramComplex (F : J ⥤ ChainComplex C ℕ) :
    ChainComplex (J ⥤ C) ℕ where
  X i := F ⋙ eval C (.down ℕ) i
  d i j := { app := fun n ↦ (F.obj n).d i j
             naturality := fun _ _ f ↦ (F.map f).comm i j }
  shape i j h := by
    apply NatTrans.ext
    funext n
    exact (F.obj n).shape i j h
  d_comp_d' i j k hij hjk := by
    apply NatTrans.ext
    funext n
    exact (F.obj n).d_comp_d i j k

/-- Evaluation of homology identifies with the original stage homologies. -/
def chainDiagramHomologyIso (F : J ⥤ ChainComplex C ℕ) (i : ℕ) :
    (chainDiagramComplex F).homology i ≅ F ⋙ homologyFunctor C (.down ℕ) i := by
  let K := chainDiagramComplex F
  refine NatIso.ofComponents (fun n ↦ ((K.sc i).mapHomologyIso
    ((evaluation J C).obj n)).symm) ?_
  intro n m f
  have h := CategoryTheory.ShortComplex.homologyMap_mapNatTrans (K.sc i)
    ((evaluation J C).map f)
  change homologyMap (F.map f) i =
    ((K.sc i).mapHomologyIso ((evaluation J C).obj n)).hom ≫ (K.homology i).map f ≫
      ((K.sc i).mapHomologyIso ((evaluation J C).obj m)).inv at h
  apply (cancel_epi ((K.sc i).mapHomologyIso ((evaluation J C).obj n)).hom).mp
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.comp_map, HomologicalComplex.homologyFunctor_map] using h.symm

variable [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

/-- Homology of the original termwise colimit complex is the colimit of stage homology. -/
def chainColimitHomologyIso (F : J ⥤ ChainComplex C ℕ) (i : ℕ) :
    ((coconeOfHasColimitEval F).pt).homology i ≅
      colimit (F ⋙ homologyFunctor C (.down ℕ) i) :=
  ((chainDiagramComplex F).sc i).mapHomologyIso (colim : (J ⥤ C) ⥤ C) ≪≫
    (colim : (J ⥤ C) ⥤ C).mapIso (chainDiagramHomologyIso F i)

/-- The homology comparison preserves each original standard inclusion into the colimit. -/
lemma chainColimitHomologyIso_ι (F : J ⥤ ChainComplex C ℕ) (i : ℕ) (n : J) :
    homologyMap ((coconeOfHasColimitEval F).ι.app n) i ≫
        (chainColimitHomologyIso F i).hom =
      colimit.ι (F ⋙ homologyFunctor C (.down ℕ) i) n := by
  let K := chainDiagramComplex F
  let τ : (evaluation J C).obj n ⟶ (colim : (J ⥤ C) ⥤ C) :=
    { app := fun D ↦ colimit.ι D n
      naturality := fun D E f ↦ (colimit.ι_map f n).symm }
  have h := CategoryTheory.ShortComplex.homologyMap_mapNatTrans (K.sc i) τ
  change homologyMap ((coconeOfHasColimitEval F).ι.app n) i =
    ((K.sc i).mapHomologyIso ((evaluation J C).obj n)).hom ≫ τ.app (K.homology i) ≫
      ((K.sc i).mapHomologyIso (colim : (J ⥤ C) ⥤ C)).inv at h
  rw [h]
  simp only [chainColimitHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  have hn := τ.naturality (chainDiagramHomologyIso F i).hom
  erw [hn.symm]
  change ((K.sc i).mapHomologyIso ((evaluation J C).obj n)).hom ≫
      ((K.sc i).mapHomologyIso ((evaluation J C).obj n)).inv ≫
        τ.app (F ⋙ homologyFunctor C (.down ℕ) i) = _
  rw [Iso.hom_inv_id_assoc]

/-- Chain homology preserves colimits of the given shape whenever those colimits are exact. -/
lemma chainHomology_preservesExactColimits (i : ℕ) :
    PreservesColimitsOfShape J (homologyFunctor C (.down ℕ) i) where
  preservesColimit {F} := by
    apply preservesColimit_of_preserves_colimit_cocone (isColimitCoconeOfHasColimitEval F)
    apply IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ homologyFunctor C (.down ℕ) i))
    refine Cocone.ext (chainColimitHomologyIso F i).symm ?_
    intro n
    apply (cancel_mono (chainColimitHomologyIso F i).hom).mp
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (chainColimitHomologyIso_ι F i n).symm

end SerrePositivity

end ExactChainHomologyColimitsPart

section ExactFunctorColimitsPart

namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂} [Category.{v₂} B]
variable {D : Type u₃} [Category.{v₃} D] [Abelian D] [HasColimitsOfShape J D]

/-- Exact diagram colimits preserve finite-limit preservation of coefficient functors. -/
instance functorColimit_preservesFiniteLimits (F : J ⥤ B ⥤ D)
    [HasExactColimitsOfShape J D] [∀ j, PreservesFiniteLimits (F.obj j)] :
    PreservesFiniteLimits (colimit F) := by
  have : PreservesFiniteLimits F.flip :=
    preservesFiniteLimits_of_evaluation _ (fun j => by
      change PreservesFiniteLimits (F.obj j)
      infer_instance)
  exact preservesFiniteLimits_of_natIso (colimitIsoFlipCompColim F).symm

/-- Pointwise colimits preserve finite-colimit preservation of coefficient functors. -/
instance functorColimit_preservesFiniteColimits (F : J ⥤ B ⥤ D)
    [∀ j, PreservesFiniteColimits (F.obj j)] : PreservesFiniteColimits (colimit F) := by
  have : PreservesFiniteColimits F.flip :=
    preservesFiniteColimits_of_evaluation _ (fun j => by
      change PreservesFiniteColimits (F.obj j)
      infer_instance)
  exact preservesFiniteColimits_of_natIso (colimitIsoFlipCompColim F).symm

end SerrePositivity

end ExactFunctorColimitsPart

section LinearFunctorColimitsPart

namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {J : Type u₁} [Category.{v₁} J]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]
variable {D : Type u₃} [Category.{v₃} D] [Preadditive D] [HasColimitsOfShape J D]

/-- Actual pointwise colimits preserve additivity of the coefficient functors. -/
instance functorColimit_additive (F : J ⥤ B ⥤ D) [∀ j, (F.obj j).Additive] :
    (colimit F).Additive where
  map_add {X Y f g} := by
    apply colimit_obj_ext
    intro j
    rw [← (colimit.ι F j).naturality (f + g), (F.obj j).map_add,
      Preadditive.add_comp, Preadditive.comp_add,
      (colimit.ι F j).naturality f, (colimit.ι F j).naturality g]

variable {A : Type*} [Semiring A] [Linear A B] [Linear A D]

/-- Actual pointwise colimits preserve linearity over the coefficient algebra. -/
instance functorColimit_linear (F : J ⥤ B ⥤ D) [∀ j, Functor.Linear A (F.obj j)] :
    Functor.Linear A (colimit F) where
  map_smul f r := by
    apply colimit_obj_ext
    intro j
    rw [← (colimit.ι F j).naturality (r • f), (F.obj j).map_smul,
      Linear.smul_comp, Linear.comp_smul, (colimit.ι F j).naturality f]

end SerrePositivity

end LinearFunctorColimitsPart
