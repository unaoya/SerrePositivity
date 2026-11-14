module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberFiberLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.ConeMapProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.ConeRotationCoordinates

/-! # 明示的 fiber 比較と回転同値の一致

概要：標準 cofiber 正方形の明示的比較は回転ホモトピー同値の順射であり、擬同型である。
方針：二つの cocone 座標を計算し、外延性で鎖写像を同定する。
規約：指定された二脚とホモトピーを保持する。使われ方：D7 の錐の比較。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open CochainComplex HomComplex
set_option backward.isDefEq.respectTransparency false
universe u
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}
/-- 回転同値の後の第一射影は二脚の対。 -/
lemma cofiberFiberRotation_projection (f : A ⟶ B) (g : A ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberRotationEquiv f g).hom ≫ mappingCocone.fst
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionC f g)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberPairMap f g := by
  apply HomologicalComplex.hom_ext
  intro p
  let d := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f g
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionC f g)
  let η := ((shiftFunctorCompIsoId (_root_.SerrePositivity.DifferentialGraded.Complex S) (1 : ℤ) (-1) (by omega)).inv.app A).f p
  let r := (mappingCone.rotateHomotopyEquiv d).hom.f (p-1)
  let s := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBiproductSignIso B C).inv.f p
  change (η ≫ r ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberOutputConeIso f g).inv.f (p-1)) ≫
      (mappingCocone.fst t).f p = _
  calc
    _ = η ≫ r ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberOutputConeIso f g).inv.f (p-1) ≫
        (mappingCone.fst t).val.v (p-1) p (by omega)) := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mappingCocone_fst_f]; exact Category.assoc _ _ _
    _ = η ≫ r ≫ ((mappingCone.fst (mappingCone.inr d)).val.v (p-1) p (by omega) ≫ s) := by
      exact congrArg (fun z => η ≫ r ≫ z) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coneMap_f_fst_v _ _ _ _ (by
        rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberOutputDifference_eq, ← Category.assoc,
          Iso.inv_hom_id, Category.id_comp]) _ _ _)
    _ = (η ≫ (r ≫ (mappingCone.fst (mappingCone.inr d)).val.v (p-1) p (by omega))) ≫ s := by
      simp only [Category.assoc]
    _ = (η ≫ ((A.shiftFunctorObjXIso 1 (p-1) p (by omega)).hom ≫ d.f p)) ≫ s := by
      exact congrArg (fun z => (η ≫ z) ≫ s) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coneRotation_fst_v d p)
    _ = d.f p ≫ s := by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.inverseDoubleShift_comp_XIso]
      exact congrArg (fun z => z ≫ s) (Category.id_comp (d.f p))
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberPairMap f g).f p := by
      change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f g ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBiproductSignIso B C).inv).f p = _
      rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberPairMap_sign, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 回転同値の第二座標は元の cone ホモトピーの負。 -/
lemma cofiberFiberRotation_snd (f : A ⟶ B) (g : A ⟶ C) (p : ℤ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberRotationEquiv f g).hom.f p ≫
      (mappingCocone.snd
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionC f g))).v p (p-1) (by omega) =
    -(mappingCone.inl (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f g)).v p (p-1) (by omega) := by
  let d := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f g
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionC f g)
  let η := ((shiftFunctorCompIsoId (_root_.SerrePositivity.DifferentialGraded.Complex S) (1 : ℤ) (-1) (by omega)).inv.app A).f p
  let r := (mappingCone.rotateHomotopyEquiv d).hom.f (p-1)
  change (η ≫ r ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberOutputConeIso f g).inv.f (p-1)) ≫
      (mappingCocone.snd t).v p (p-1) (by omega) = _
  calc
    _ = η ≫ r ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberOutputConeIso f g).inv.f (p-1) ≫
        (mappingCone.snd t).v (p-1) (p-1) (add_zero _)) := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mappingCocone_snd_v]; exact Category.assoc _ _ _
    _ = η ≫ r ≫ ((mappingCone.snd (mappingCone.inr d)).v (p-1) (p-1) (add_zero _) ≫
        (𝟙 (mappingCone d) : mappingCone d ⟶ mappingCone d).f (p-1)) := by
      exact congrArg (fun z => η ≫ r ≫ z) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coneMap_f_snd_v _ _ _ _ (by
        rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberOutputDifference_eq, ← Category.assoc,
          Iso.inv_hom_id, Category.id_comp]) _)
    _ = η ≫ (r ≫ (mappingCone.snd (mappingCone.inr d)).v (p-1) (p-1) (add_zero _)) := by
      simp only [HomologicalComplex.id_f, Category.comp_id]
    _ = η ≫ (-((A.shiftFunctorObjXIso 1 (p-1) p (by omega)).hom ≫
        (mappingCone.inl d).v p (p-1) (by omega))) := by
      exact congrArg (fun z => η ≫ z) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.coneRotation_snd_v d p)
    _ = -(mappingCone.inl d).v p (p-1) (by omega) := by
      rw [Preadditive.comp_neg, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.inverseDoubleShift_comp_XIso]
      exact congrArg Neg.neg (Category.id_comp _)

/-- 回転同値の順射は標準正方形の明示的な fiber 比較そのもの。 -/
lemma cofiberFiberRotation_hom_eq_lift (f : A ⟶ B) (g : A ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberRotationEquiv f g).hom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mappingCocone_hom_ext
  · rw [cofiberFiberRotation_projection, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberProjection_eq_mappingCocone_fst,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift_projection]
  · intro p q hpq
    obtain rfl : q = p-1 := by omega
    rw [cofiberFiberRotation_snd, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift_snd]

/-- 二脚と標準ホモトピーを保持する比較射はホモトピー同値。 -/
lemma cofiberFiberLift_homotopyEquivalence (f : A ⟶ B) (g : A ⟶ C) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} S) (.up ℤ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberRotationEquiv f g, cofiberFiberRotation_hom_eq_lift f g⟩

/-- 標準 cofiber 正方形の明示的な fiber 比較は擬同型。 -/
lemma cofiberFiberLift_quasiIso (f : A ⟶ B) (g : A ⟶ C) :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g) := by
  rw [← cofiberFiberRotation_hom_eq_lift]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
