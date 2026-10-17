module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfHomComparisonDegrees
public import SerrePositivity.DifferentialGraded.Tensor.UnitBimoduleIso
public import SerrePositivity.DifferentialGraded.Morita.KernelAugmentation

/-! # 表現可能加群上の通常・主導来 kernel 作用の自然な計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- Yoneda の後に通常 tensor を適用する dg 関手は、対角との合成そのもの。 -/
lemma criterionPerfYonedaTensor_eq :
    (dgYoneda A D).comp (kernelTensor A D E P) =
      (BimoduleTensor.compose A E D D P (Bimodule.diagonal A D)).toFunctor := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (dgYoneda A D).comp (kernelTensor A D E P))
    (G := (BimoduleTensor.compose A E D D P (Bimodule.diagonal A D)).toFunctor)
    (fun _ => rfl)
  intro d d'
  simp only [eqToHom_refl, Category.comp_id]
  apply moduleHom_ext A E
  intro e
  change ((dgYoneda A D).map d d' ≫ (kernelTensor A D E P).map _ _) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (dgYoneda A D).map d d' ≫ k)
      (kernelTensor_map_π A D E P (representable A d) (representable A d') e)).trans
        (BimoduleTensor.compose_leftMap_π A E D D P (Bimodule.diagonal A D) d d' e).symm)

/-- 対角の右単位を、表現可能対象上の通常 tensor の自然同型にする。 -/
def criterionPerfYonedaTensorIso :
    (dgYoneda A D).onClosed ⋙ (kernelTensor A D E P).onClosed ≅ P.toFunctor.onClosed := by
  let e := eqToIso (congrArg (fun F : DGFunctor A D (RightModule A E) => F.onClosed)
    (criterionPerfYonedaTensor_eq A D E P))
  refine e ≪≫ NatIso.ofComponents (fun d => BimoduleTensor.rightUnitIso A E D P d) ?_
  intro d d' f
  exact (kernelClosedFamilyNatTrans A E D
    (BimoduleTensor.rightBimoduleUnitIso A E D P).hom).naturality f

/-- 表現可能対象上の導来作用の計算は、閉零射にも自然な同型である。 -/
def criterionPerfYonedaDerivedIso :
    (dgYoneda A D).onClosed ⋙ moduleToDerived A D ⋙
        kernelDerivedTensorOnBimodule A D E P ≅ P.toFunctor.onClosed ⋙ moduleToDerived A E := by
  let e : (dgYoneda A D).onClosed ⋙ moduleToDerived A D ⋙
      kernelDerivedTensorOnBimodule A D E P ≅
      (dgYoneda A D).onClosed ⋙ (kernelTensor A D E P).onClosed ⋙ moduleToDerived A E :=
    NatIso.ofComponents
      (fun d => kernelRelativeKFlatComputation A D E P _
        (moduleHomotopicallyProjective_relativeKFlat A D
          (representable_homotopicallyProjective A D d)))
      (fun f => (kernelDerivedTensorAugmentation A D E P).naturality
        ((dgYoneda A D).onClosed.map f))
  exact e ≪≫ isoWhiskerRight (criterionPerfYonedaTensorIso A D E P) (moduleToDerived A E)

/-- 指定主局所化の実際の kernel 関手そのものの、表現可能対象上の自然な計算。 -/
def criterionPerfYonedaMainDerivedIso :
    (dgYoneda A D).onClosed ⋙ moduleToDerived A D ⋙
        kernelDerivedTensor A D E
          ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P)) ≅
      P.toFunctor.onClosed ⋙ moduleToDerived A E :=
  isoWhiskerLeft ((dgYoneda A D).onClosed ⋙ moduleToDerived A D)
    (kernelDerivedTensorOnBimoduleIso A D E (BimoduleCategory.of A E D P)) ≪≫
      criterionPerfYonedaDerivedIso A D E P

/-- 実際の主作用の射を、列の主導来対象間の射として読む。 -/
def criterionPerfYonedaMainActionMap (d d' : ClosedCategory A D)
    (f : criterionPerfRepresentable A D d ⟶ criterionPerfRepresentable A D d') :
    (moduleToDerived A E).obj (criterionPerfColumn A D E P d) ⟶
      (moduleToDerived A E).obj (criterionPerfColumn A D E P d') :=
  (criterionPerfYonedaMainDerivedIso A D E P).inv.app d ≫
    (kernelDerivedTensor A D E
      ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map f ≫
    (criterionPerfYonedaMainDerivedIso A D E P).hom.app d'

/-- 元の dg 圏の閉零射に対して、主作用の射計算は列の左作用の局所化と一致する。 -/
lemma criterionPerfYonedaMainActionMap_closed {d d' : ClosedCategory A D} (f : d ⟶ d') :
    criterionPerfYonedaMainActionMap A D E P d d'
        ((moduleToDerived A D).map ((dgYoneda A D).onClosed.map f)) =
      (moduleToDerived A E).map (P.toFunctor.onClosed.map f) := by
  have h := (criterionPerfYonedaMainDerivedIso A D E P).hom.naturality f
  change _ ≫ (criterionPerfYonedaMainDerivedIso A D E P).hom.app d' =
    (criterionPerfYonedaMainDerivedIso A D E P).hom.app d ≫
      (moduleToDerived A E).map (P.toFunctor.onClosed.map f) at h
  exact (congrArg (fun k => (criterionPerfYonedaMainDerivedIso A D E P).inv.app d ≫ k) h).trans
    (Iso.inv_hom_id_app_assoc _ _ _)

/-- 閉零射の全 Hom 比較の H⁰ は、実際の主 kernel 作用の射写像である。 -/
lemma criterionPerfYonedaMainActionMap_homology_zero {d d' : ClosedCategory A D}
    (f : d ⟶ d') (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    criterionPerfColumnDerivedHomEquiv A D E P d d' R
        (criterionPerfYonedaMainActionMap A D E P d d'
          ((moduleToDerived A D).map ((dgYoneda A D).onClosed.map f))) =
      HomologicalComplex.homologyMap (criterionPerfHomComparison A D E P d d' R) 0
        (complexZeroHomologyClass A (homObject A D d d') (closedHomEquiv A D d d' f)) := by
  rw [criterionPerfYonedaMainActionMap_closed]
  exact criterionPerfHomComparison_homology_zero A D E P f R

end SerrePositivity.DifferentialGraded.Morita
