module
public import SerrePositivity.DifferentialGraded.Complexes.ConeHom
public import SerrePositivity.DifferentialGraded.Module.ClosedMaps

/-! # 全次数作用を持つ右 dg 加群の cone 対象 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 加群作用は閉単位を恒等 cochain に移す。 -/
lemma moduleMap_unit_cochain (M : RightModule A D) (x : Dᵒᵖ) :
    (M.map x x).f 0 (unitElement A x).val = Cochain.ofHom (𝟙 (M.obj x)) := by
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (M.toFunctor.map_id x)
  rw [cycleFromUnit_postcomp] at h
  change (M.map x x).f 0 (unitElement A x).val =
    (cycleFromUnit _ (identity (M.obj x))).val at h
  simpa only [identity, cycleFromUnit_unitFromCycle] using h

/-- 加群作用の豊穣順合成を cochain 全体で読む。 -/
lemma moduleMap_forward (M : RightModule A D) {x y z : Dᵒᵖ} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hn : p + q = n) :
    (M.map x z).f n (forward A f g hn) =
      (p * q).negOnePow • ((M.map x y).f p f).comp ((M.map y z).f q g) hn := by
  have h := congrArg (fun l => l.f n
    (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g)))
    (M.toFunctor.map_comp x y z)
  change (M.map x z).f n (forward A f g hn) =
    (enrichedComposition _ _ _).f n
      ((M.map x y ⊗ₘ M.map y z).f n
        (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g))) at h
  rw [tensorMap_apply, enrichedComposition_apply] at h
  exact h

variable {A}
/-- 全次数自然な閉零射族の objectwise mapping cone とその dg 作用。 -/
abbrev coneModule (M N : RightModule A D)
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) : RightModule A D where
  obj x := mappingCone (a x)
  map x y := coneHomMap (a x) (a y) (M.map x y) (N.map x y) (h x y)
  map_id x := by
    apply (unitCycleEquiv _).injective
    apply Subtype.ext
    change (cycleFromUnit _ (eId (Complex A) x ≫
      coneHomMap (a x) (a x) (M.map x x) (N.map x x) (h x x))).val =
        (cycleFromUnit _ (identity (mappingCone (a x)))).val
    rw [cycleFromUnit_postcomp]
    change coneMapCochain (a x) (a x)
      ((M.map x x).f 0 (unitElement A x).val) ((N.map x x).f 0 (unitElement A x).val) = _
    rw [moduleMap_unit_cochain, moduleMap_unit_cochain]
    simp only [identity, cycleFromUnit_unitFromCycle]
    exact coneMapCochain_identity (a x)
  map_comp x y z := by
    apply tensorHom_ext
    intro p q n hn
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f g
    change coneMapCochain (a x) (a z)
      ((M.map x z).f n (forward A f g hn)) ((N.map x z).f n (forward A f g hn)) =
      (enrichedComposition _ _ _).f n
        ((coneHomMap (a x) (a y) (M.map x y) (N.map x y) (h x y) ⊗ₘ
          coneHomMap (a y) (a z) (M.map y z) (N.map y z) (h y z)).f n
            (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g)))
    rw [tensorMap_apply, enrichedComposition_apply, coneHomMap_apply, coneHomMap_apply,
      moduleMap_forward, moduleMap_forward, coneMapCochain_units_smul,
      coneMapCochain_comp]

variable (A D) [Small.{u} D]
/-- 主閉零加群圏の射の cone。 -/
abbrev moduleCone {M N : ModuleCategory A D} (f : M ⟶ N) : ModuleCategory A D :=
  ForgetEnrichment.of (Complex A) (coneModule (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)
    (closedTransApp A (moduleClosedHomEquiv A D M N f))
    (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f)))

/-- 評価すると既存 Mathlib の mapping cone と同じ複体になる。 -/
lemma moduleCone_eval {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).obj (moduleCone A D f) =
      mappingCone ((moduleEvaluation A D x).map f) := rfl

/-- cone の標準包含は全次数自然な加群射。 -/
def moduleConeInr {M N : ModuleCategory A D} (f : M ⟶ N) : N ⟶ moduleCone A D f :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) N)
    (N := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (fun x => mappingCone.inr (closedTransApp A (moduleClosedHomEquiv A D M N f) x))
    (fun x y => coneHomMap_inr _ _ _ _
      (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f) x y))

/-- 標準包含の評価は Mathlib の標準包含。 -/
@[simp] lemma moduleConeInr_eval {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleConeInr A D f) =
      mappingCone.inr ((moduleEvaluation A D x).map f) := by
  unfold moduleConeInr
  rw [moduleMorphismMk_eval]
  rfl
end SerrePositivity.DifferentialGraded
