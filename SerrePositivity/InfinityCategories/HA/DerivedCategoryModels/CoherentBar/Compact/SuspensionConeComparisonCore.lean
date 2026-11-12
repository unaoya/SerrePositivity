module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.FullFunctor
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionIdentity
public import SerrePositivity.KST.SConstruction.DGFunctorClosedFamilyIso
public import SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugation

/-!
概要：実全 Hom の共役と恒等加群延長を、同じ dg 関手 end の閉同型へ束ねる。
方針：自然性を一般の小さい源で証明し、具体的な代表選択の展開を避ける。
規約：cell 分解や固定収縮との整合は別境界である。
使われ方：固定 cone 作用の単位・合成比較の共通部品。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded KST.SConstruction KST.NonConnective
variable (R : Type u) [CommRing R]

/-- 全 Hom の実共役の比較を、同じ dg 関手圏の閉同型にする。 -/
def dgClosedConjugationComparison {X : Type v} [DGCategory R X] [Small.{u} X]
    {Y : Type w} [DGCategory R Y] (F : DGFunctor R X Y) (b : X → Y)
    (e : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ≅
      ForgetEnrichment.of (Complex R) (b x)) :
    ForgetEnrichment.of (Complex R) F ≅
      ForgetEnrichment.of (Complex R) (dgFunctorClosedConjugate R F b e) :=
  dgFunctorClosedIsoFromFamily R X Y F (dgFunctorClosedConjugate R F b e) e
    (dgFunctorClosedConjugate_naturality R F b e)

/-- 任意の小さい源からの評価後でも、恒等加群延長の全 Hom 比較を保持する。 -/
def dgModuleIdentityPrecompositionIso
    (A : Type v) [DGCategory R A] [Small.{u} A]
    {X : Type w} [DGCategory R X] [Small.{u} X]
    (E : DGFunctor R X (RightModule R A)) :
    ForgetEnrichment.of (Complex R) (E.comp (dgModuleExtension R A A (DGFunctor.id A))) ≅
      ForgetEnrichment.of (Complex R) E :=
  dgFunctorClosedIsoFromFamily R X (RightModule R A)
    (E.comp (dgModuleExtension R A A (DGFunctor.id A))) E
    (fun x => dgModuleExtensionIdentityAt R A (E.obj x)) (fun x y => by
      change (E.map x y ≫ (dgModuleExtension R A A (DGFunctor.id A)).map _ _) ≫
        moduleHomPostcompose R A _ _ _ (dgModuleExtensionIdentityAt R A (E.obj y)).hom =
          E.map x y ≫ moduleHomPrecompose R A _ _ _
            (dgModuleExtensionIdentityAt R A (E.obj x)).hom
      rw [Category.assoc, dgModuleExtensionIdentityAt_naturality])

/-- 代表化の比較を、同じ dg 関手 end 内の閉同型へ束ねる一般入口。 -/
def dgModuleStrictImageComparisonIso
    (C : Type v) [DGCategory R C] [Small.{u} C]
    (D : Type w) [DGCategory R D] [Small.{u} D]
    (F : DGFunctor R (RightModule R C) (RightModule R D))
    (S : Set (ModuleCategory R C)) (T : Set (ModuleCategory R D))
    [Small.{u} {M // S M}] (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R C D F S T) :
    ForgetEnrichment.of (Complex R)
      (((dgFullSubcategoryInclusion R (ModuleCategory R C) S).comp
        (dgConeModuleForget R C)).comp F) ≅
      ForgetEnrichment.of (Complex R)
        ((e.functor R C D F S T).comp
          ((dgFullSubcategoryInclusion R (ModuleCategory R D) T).comp
            (dgConeModuleForget R D))) := by
  refine dgFunctorClosedIsoFromFamily R {M // S M} (RightModule R D) _ _ e.iso ?_
  intro M N
  let L := ((dgFullSubcategoryInclusion R (ModuleCategory R C) S).comp
    (dgConeModuleForget R C)).comp F
  change L.map M N ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (L.obj M)) (e.iso N).hom =
    ((e.evaluated R C D F S T).map M N ≫ 𝟙 _) ≫
      eHomWhiskerRight (Complex R) (e.iso M).hom
        (ForgetEnrichment.of (Complex R) (ForgetEnrichment.to (Complex R) (e.obj N).val))
  rw [Category.comp_id]
  exact dgFunctorClosedConjugate_naturality R L
    (fun M => ForgetEnrichment.to (Complex R) (e.obj M).val) e.iso M N

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
