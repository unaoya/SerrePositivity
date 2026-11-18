module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseOperad
public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseDifferentialAdjunction
public import SerrePositivity.EInfinity.BarrattEccles.Theory.OperadTransportAdjunction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FreeAlgebraAdjunction
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# 微分を消したオペラッド代数の随伴

## 概要
Berger–Moerdijk 命題 4.1 のセル付加の pushout を次数付きの台で読む。

## 方針
複体上の随伴と arity の恒等比較を用いて、随伴をオペラッド代数に持ち上げる。

## 規約
部分合成と Koszul 対称性を保つ。

## 使われ方
付加の pushout と自由代数が次数付きの台への移送と可換になる。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits MonoidalCategory DifferentialGraded
open Functor.LaxMonoidal Functor.OplaxMonoidal

section AdjunctionMates
variable {S T : Type u} [CommRing S] [CommRing T]
  {L : Complex S ⥤ Complex T} {R : Complex T ⥤ Complex S}
  [L.Monoidal] [R.LaxMonoidal] (a : L ⊣ R) [a.IsMonoidal]

/-- The unit of a monoidal adjunction compares transported nullary structure maps. -/
lemma adjunctionUnit_image_unit {X : Complex S} (f : 𝟙_ (Complex S) ⟶ X) :
    f ≫ a.unit.app X = ε R ≫ R.map (ε L ≫ L.map f) := by
  apply (a.homEquiv _ _).symm.injective
  rw [a.homEquiv_naturality_left_symm, Adjunction.homEquiv_symm_unit,
    Category.comp_id, a.homEquiv_naturality_right_symm, laxUnit_mate,
    ← Category.assoc, Functor.Monoidal.η_ε, Category.id_comp]

/-- The unit of a monoidal adjunction compares transported binary structure maps. -/
lemma adjunctionUnit_image_comp {X Y Z : Complex S} (f : X ⊗ Y ⟶ Z) :
    f ≫ a.unit.app Z = ((a.unit.app X ⊗ₘ a.unit.app Y) ≫ μ R _ _) ≫
      R.map (μ L X Y ≫ L.map f) := by
  apply (a.homEquiv _ _).symm.injective
  rw [a.homEquiv_naturality_left_symm, Adjunction.homEquiv_symm_unit,
    Category.comp_id, a.homEquiv_naturality_right_symm]
  change L.map f = (a.homEquiv _ _).symm
    (laxTensorComparison R (a.unit.app X) (a.unit.app Y)) ≫ (μ L X Y ≫ L.map f)
  rw [laxTensorComparison_mate]
  simp only [CategoryTheory.Functor.id_obj, Adjunction.homEquiv_symm_unit,
    tensorHom_id, id_whiskerRight, Category.comp_id, Functor.Monoidal.δ_μ_assoc]
end AdjunctionMates

variable (A : Type u) [CommRing A]

instance cofreeCycles_laxMonoidal : (cofreeCycles A).LaxMonoidal :=
  (eraseDifferentialAdjunction A).rightAdjointLaxMonoidal

instance eraseDifferentialAdjunction_isMonoidal :
    (eraseDifferentialAdjunction A).IsMonoidal := inferInstance

@[reassoc]
lemma eraseDifferential_map_braiding_delta (X Y : Complex A) :
    (eraseDifferential A).map (β_ X Y).hom ≫ δ (eraseDifferential A) Y X =
      δ (eraseDifferential A) X Y ≫
        (β_ ((eraseDifferential A).obj X) ((eraseDifferential A).obj Y)).hom := by
  let L := eraseDifferential A
  apply (cancel_mono (μ L Y X)).mp
  change (eraseDifferential A).map (β_ X Y).hom ≫
    δ (eraseDifferential A) Y X ≫ μ (eraseDifferential A) Y X = _
  rw [Functor.Monoidal.δ_μ, Category.comp_id, Category.assoc,
    ← Functor.LaxBraided.braided, Functor.Monoidal.δ_μ_assoc]

instance cofreeCycles_laxBraided : (cofreeCycles A).LaxBraided where
  toLaxMonoidal := cofreeCycles_laxMonoidal A
  braided X Y := by
    let L := eraseDifferential A
    let R := cofreeCycles A
    let a := eraseDifferentialAdjunction A
    apply (a.homEquiv _ _).symm.injective
    simp only [a.homEquiv_counit, CategoryTheory.Functor.map_comp, Category.assoc,
      a.counit_naturality, a.map_μ_comp_counit_app_tensor,
      a.map_μ_comp_counit_app_tensor_assoc]
    rw [eraseDifferential_map_braiding_delta_assoc, BraidedCategory.braiding_naturality]

attribute [local irreducible] cofreeCycles

variable {A} (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A)

/-- The identity arity comparison into the erased operad. -/
def Operad.eraseComparison : Operad.LaxComparison (eraseDifferential A) P.erase P where
  arity _ := 𝟙 _
  permutation _ _ := by
    simp [LaxComparisonSquare, Operad.erase]
    rfl
  unit := by
    simp [LaxComparisonSquare, Operad.erase]
    rfl
  comp _ _ _ := by
    simp [LaxComparisonSquare, laxTensorComparison, Operad.erase]
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (eraseComparison)

/-- The mate of the erased arity comparison. -/
def Operad.cofreeComparison : Operad.LaxComparison (cofreeCycles A) P P.erase where
  arity n := (eraseDifferentialAdjunction A).unit.app (P.arity n)
  permutation _ _ := (eraseDifferentialAdjunction A).unit.naturality _
  unit := by
    let a := eraseDifferentialAdjunction A
    let R := cofreeCycles A
    change P.unit ≫ a.unit.app (P.arity 1) =
      ε R ≫ R.map (ε (eraseDifferential A) ≫ (eraseDifferential A).map P.unit)
    exact adjunctionUnit_image_unit a P.unit

  comp m n i := by
    let L := eraseDifferential A
    let R := cofreeCycles A
    let a := eraseDifferentialAdjunction A
    let X := P.arity (m + 1)
    let Y := P.arity n
    let c := P.comp m n i
    change c ≫ a.unit.app (P.arity (m + n)) =
      ((a.unit.app X ⊗ₘ a.unit.app Y) ≫ μ R _ _) ≫ R.map (μ L X Y ≫ L.map c)
    exact adjunctionUnit_image_comp a c

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (cofreeComparison)

/-- Erasing the differential of an algebra and its operations. -/
def Operad.eraseAlgebra : P.Algebra ⥤ P.erase.Algebra :=
  Operad.transport P.eraseComparison

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (eraseAlgebra)

/-- Erasing the differential of an operad algebra is a left adjoint. -/
def Operad.eraseAlgebraAdjunction :
    P.eraseAlgebra ⊣ Operad.transport P.cofreeComparison := by
  letI : ∀ n, IsIso (P.eraseComparison.arity n) := fun n => by
    change IsIso (𝟙 ((eraseDifferential A).obj (P.arity n)))
    infer_instance
  apply Operad.transportAdjunction (eraseDifferentialAdjunction A)
    (eraseDifferentialAdjunction_isMonoidal A)
  intro n
  change ((eraseDifferentialAdjunction A).homEquiv _ _).symm
    ((eraseDifferentialAdjunction A).unit.app (P.arity n)) = _
  simp only [CategoryTheory.Functor.id_obj, Adjunction.homEquiv_symm_unit]
  symm
  exact IsIso.inv_id

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (eraseAlgebraAdjunction)

instance Operad.eraseAlgebra_isLeftAdjoint : P.eraseAlgebra.IsLeftAdjoint :=
  P.eraseAlgebraAdjunction.isLeftAdjoint

/-- The erased free algebra is free on the erased complex, compatibly with all generator maps. -/
def Operad.eraseFreeAlgebraIso :
    P.freeAlgebraFunctor ⋙ P.eraseAlgebra ≅
      eraseDifferential A ⋙ P.erase.freeAlgebraFunctor :=
  Adjunction.leftAdjointUniq
    (P.freeAlgebraAdjunction.comp P.eraseAlgebraAdjunction)
    ((eraseDifferentialAdjunction A).comp P.erase.freeAlgebraAdjunction)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (eraseFreeAlgebraIso)

end SerrePositivity.EInfinity
