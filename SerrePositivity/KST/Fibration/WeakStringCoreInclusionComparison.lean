module
public import SerrePositivity.KST.Fibration.WeakStringConstantCoreInclusion
public import SerrePositivity.KST.Fibration.WeakStringRelativeMultiRealization

/-! # 元の相対 S への core 包含を、同じ定数 W 列へ運ぶ実比較の局所化等式 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の core S 包含は、相対 S の実比較の後で元の定数 W 列の core S 実現になる。 -/
theorem relativeSWeakStringCoreComparison_coreInclusion
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    AnodyneHomotopy.anodyneQ.map (simplicialDiagonalFunctor.map
      (relativeSimplicialSConstructionCoreInclusion q.hom)) ≫
      AnodyneHomotopy.anodyneQ.map (relativeSWeakStringCoreComparison q) =
        AnodyneHomotopy.anodyneQ.map
          (weakStringRealizationConstantDiagonal coreSRealizationFunctor q) := by
  let Q := AnodyneHomotopy.anodyneQ
  let a : objectSConstruction B.obj ⟶ coreSRealizationFunctor.obj (sInputModel B) :=
    objectToCoreSRealization B.obj
  let i : coreSRealizationFunctor.obj (sInputModel B) ⟶
      simplicialDiagonalFunctor.obj (relativeSimplicialSConstruction q.hom) :=
    simplicialDiagonalFunctor.map (relativeSimplicialSConstructionCoreInclusion q.hom)
  let c := relativeSWeakStringCoreComparison q
  let k := weakStringRealizationConstantDiagonal coreSRealizationFunctor q
  have h : a ≫ i ≫ c = a ≫ k :=
    relativeSWeakStringCoreComparison_coreInclusion_object q
  have : IsIso (Q.map a) := objectToCoreSRealization_localized_isIso B.obj
  change Q.map i ≫ Q.map c = Q.map k
  apply (cancel_epi (Q.map a)).1
  rw [← Q.map_comp, ← Q.map_comp, ← Q.map_comp]
  exact congrArg Q.map h

/-- 同じ定数包含を core S と単回反復実現の座標同型が保つ。 -/
lemma weakStringConstantDiagonal_coreSingle {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (coreSingleRealizationIso (sInputModel B)).hom ≫
      weakStringRealizationConstantDiagonal (multiRealizationFunctor 1) q =
        weakStringRealizationConstantDiagonal coreSRealizationFunctor q ≫
          simplicialDiagonalFunctor.map (weakStringCoreSingleRealizationIso q).hom := by
  let e : coreSRealizationFunctor.{u} ≅ multiRealizationFunctor 1 :=
    NatIso.ofComponents coreSingleRealizationIso (by
      intro X Y f
      exact coreSingleRealizationIso_naturality f)
  exact weakStringRealizationConstantDiagonal_naturality e.hom q

/-- 元の core 包含は、有限加法性と同じ単回反復実現への実比較でも同じ定数包含になる。 -/
theorem relativeSWeakStringMultiComparison_coreInclusion
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    AnodyneHomotopy.anodyneQ.map (simplicialDiagonalFunctor.map
      (relativeSimplicialSConstructionCoreInclusion q.hom)) ≫
      AnodyneHomotopy.anodyneQ.map (relativeSWeakStringMultiComparison q) =
        AnodyneHomotopy.anodyneQ.map
          ((coreSingleRealizationIso (sInputModel B)).hom ≫
            weakStringRealizationConstantDiagonal (multiRealizationFunctor 1) q) := by
  let Q := AnodyneHomotopy.anodyneQ
  let Y := simplicialDiagonalFunctor.obj
    (weakStringStableSimplicial q ⋙ coreSRealizationFunctor)
  let Z := simplicialDiagonalFunctor.obj (weakStringMultiRealization q 1)
  let k : coreSRealizationFunctor.obj (sInputModel B) ⟶ Y :=
    weakStringRealizationConstantDiagonal coreSRealizationFunctor q
  let j : Y ⟶ Z := simplicialDiagonalFunctor.map (weakStringCoreSingleRealizationIso q).hom
  let p : coreSRealizationFunctor.obj (sInputModel B) ⟶
      (multiRealizationFunctor 1).obj (sInputModel B) :=
    (coreSingleRealizationIso (sInputModel B)).hom
  let l : (multiRealizationFunctor 1).obj (sInputModel B) ⟶ Z :=
    weakStringRealizationConstantDiagonal (multiRealizationFunctor 1) q
  have he : p ≫ l = k ≫ j := weakStringConstantDiagonal_coreSingle q
  unfold relativeSWeakStringMultiComparison
  rw [Functor.map_comp, ← Category.assoc, relativeSWeakStringCoreComparison_coreInclusion]
  change Q.map k ≫ Q.map j = Q.map (p ≫ l)
  rw [← Q.map_comp, ← he]

end SerrePositivity.KST.Fibration
