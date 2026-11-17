module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechGlobalAugmentation
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleAugmented

/-!
概要：同じ nerve の各項の大域切断を、同じタプル被覆複体へ自然に増大する。
方針：恒等スカラーの既存の増大を single からの射にし、実際の Γ の写像と照合する。
規約：元の nerve、係数、等号判定、タプル被覆と全ての射を保持する。
使われ方：環の conerve の係数と同じ二重 Čech の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime)
variable (h : ∀ n : SimplexCategoryᵒᵖ,
  ∀ O, (p : ((Arrow.mk f).cechNerve.obj n).presheaf.obj O) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ nerve 項の大域切断の係数から、同じタプル複体への実際の増大。 -/
def schemePerfectCechTupleGlobalAugmentationHom (n : SimplexCategory) :
    (HomologicalComplex.single (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) 0).obj
      (ModuleCat.of ℤ (FrobeniusDirectLimit
        Γ((Arrow.mk f).cechNerve.obj (op n), ⊤) p hp (h (op n) (op ⊤)))) ⟶
      schemePerfectCechTupleComplex f U p hp h n := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  exact HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom (schemeStructurePerfectCechAugmentation
      ((Arrow.mk f).cechNerve.obj (op n)) (RingHom.id _) p hp (h (op n) (op ⊤))
      (h (op n)) (schemeCechTupleOpen f U (op n)))) (by
        intro k hk
        have he : k = 1 := Eq.symm hk
        clear hk
        subst k
        apply ModuleCat.hom_ext
        simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
          schemePerfectCechTupleComplex] using
          schemeStructurePerfectCechAugmentation_cycle
            ((Arrow.mk f).cechNerve.obj (op n)) (RingHom.id _) p hp (h (op n) (op ⊤))
            (h (op n)) (schemeCechTupleOpen f U (op n)))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ single からの射の零次成分は恒等スカラーの実際の増大。 -/
theorem schemePerfectCechTupleGlobalAugmentationHom_f_zero (n : SimplexCategory) :
    (schemePerfectCechTupleGlobalAugmentationHom f U p hp h n).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
        (ModuleCat.of ℤ (FrobeniusDirectLimit
          Γ((Arrow.mk f).cechNerve.obj (op n), ⊤) p hp (h (op n) (op ⊤))))).hom ≫
        ModuleCat.ofHom (by
          letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
          exact schemeStructurePerfectCechAugmentation
            ((Arrow.mk f).cechNerve.obj (op n)) (RingHom.id _) p hp
            (h (op n) (op ⊤)) (h (op n)) (schemeCechTupleOpen f U (op n))) := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  exact HomologicalComplex.mkHomFromSingle_f _ _

set_option backward.isDefEq.respectTransparency false in
/-- 元の nerve の Γ の係数写像と同じタプル被覆の射は、同じ大域増大と可換。 -/
theorem schemePerfectCechTupleGlobalAugmentationHom_naturality
    {m n : SimplexCategory} (a : m ⟶ n) :
    schemePerfectCechTupleGlobalAugmentationHom f U p hp h m ≫
        schemePerfectCechTupleMap f U p hp h a =
      (HomologicalComplex.single (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) 0).map
        ((frobeniusRingDiagram ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ) p hp
          (fun n ↦ h (op n) (op ⊤))).map a) ≫
        schemePerfectCechTupleGlobalAugmentationHom f U p hp h n := by
  letI := cechFiniteIndexOrder (Fin (m.len + 1) → ι)
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  apply HomologicalComplex.from_single_hom_ext
  have h0 : ModuleCat.ofHom (schemeStructurePerfectCechAugmentation
      ((Arrow.mk f).cechNerve.obj (op m)) (RingHom.id _) p hp (h (op m) (op ⊤))
      (h (op m)) (schemeCechTupleOpen f U (op m))) ≫
      (schemePerfectCechTupleMap f U p hp h a).f 0 =
    ((frobeniusRingDiagram ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ) p hp
      (fun n ↦ h (op n) (op ⊤))).map a) ≫
      ModuleCat.ofHom (schemeStructurePerfectCechAugmentation
        ((Arrow.mk f).cechNerve.obj (op n)) (RingHom.id _) p hp (h (op n) (op ⊤))
        (h (op n)) (schemeCechTupleOpen f U (op n))) := by
    apply ModuleCat.hom_ext
    exact schemeStructurePerfectCechRefinedPullbackMap_globalAugmentation
      ((Arrow.mk f).cechNerve.map a.op) p hp (h (op m)) (h (op n))
      (schemeCechTupleOpen f U (op m)) (schemeCechTupleOpen f U (op n))
      (fun t j ↦ t (a.toOrderHom j)) (schemeCechTupleOpen_map_le f U a.op)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    schemePerfectCechTupleGlobalAugmentationHom_f_zero,
    schemePerfectCechTupleGlobalAugmentationHom_f_zero, HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun k ↦ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
    (ModuleCat.of ℤ (FrobeniusDirectLimit
      Γ((Arrow.mk f).cechNerve.obj (op m), ⊤) p hp (h (op m) (op ⊤))))).hom ≫ k) h0

/-- 同じ実際の大域切断の係数図式から同じタプル複体への自然な増大。 -/
def schemePerfectCechTupleGlobalAugmentation :
    frobeniusRingDiagram ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ) p hp
        (fun n ↦ h (op n) (op ⊤)) ⋙
        HomologicalComplex.single (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) 0 ⟶
      schemePerfectCechTupleFunctor f U p hp h where
  app := schemePerfectCechTupleGlobalAugmentationHom f U p hp h
  naturality _ _ a := (schemePerfectCechTupleGlobalAugmentationHom_naturality f U p hp h a).symm

end SerrePositivity.AlgebraicGeometry
