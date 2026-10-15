module
public import SerrePositivity.DifferentialGraded.Tensor.Balanced
public import SerrePositivity.DifferentialGraded.Tensor.Elements
public import SerrePositivity.DifferentialGraded.Module.LeftRing
public import SerrePositivity.DifferentialGraded.Module.TensorUnit

/-! # 一対象環上のbalanced tensorと通常の非有界tensorの比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A]

lemma ring_rightAction (M : RightModule A PUnit.{1}) (x : PUnit.{1}) :
    rightAction A PUnit.{1} M x x = (ρ_ (M.obj (op x))).hom := by
  change (signedSwap (M.obj (op x)) (𝟙_ (Complex A))).hom ≫
    uncurryRight (M.map (op x) (op x)) = _
  rw [ringModule_map, uncurryRight_identity]
  exact braiding_leftUnitor _

lemma ring_leftAction (N : LeftModule A PUnit.{1}) (x : PUnit.{1}) :
    leftAction A PUnit.{1} N x x = (λ_ (N.obj x)).hom := by
  unfold leftAction
  rw [ringLeftModule_map, uncurryRight_identity]

/-- 一対象環では恒等tensor写像の族がbalancedである。 -/
def ringFamily (M : RightModule A PUnit.{1}) (N : LeftModule A PUnit.{1}) :
    BalancedFamily A PUnit.{1} M N (M.obj (op PUnit.unit) ⊗ N.obj PUnit.unit) := by
  refine ⟨fun x => by cases x; exact 𝟙 _, ?_⟩
  intro x y
  cases x
  cases y
  simp only [Category.comp_id, ring_rightAction, ring_leftAction]
  monoidal_coherence

/-- 任意の一対象dg加群のbalanced tensorは値の通常tensorに同型。 -/
def ringIso (M : RightModule A PUnit.{1}) (N : LeftModule A PUnit.{1}) :
    obj A PUnit.{1} M N ≅ M.obj (op PUnit.unit) ⊗ N.obj PUnit.unit where
  hom := desc A PUnit.{1} M N (ringFamily A M N)
  inv := ι A PUnit.{1} M N PUnit.unit
  hom_inv_id := by
    apply hom_ext
    intro x
    cases x
    rw [ι_desc_assoc]
    simp only [ringFamily, Category.id_comp, Category.comp_id]
  inv_hom_id := ι_desc A PUnit.{1} M N (ringFamily A M N) PUnit.unit

@[reassoc (attr := simp)]
lemma ι_ringIso_hom (M : RightModule A PUnit.{1}) (N : LeftModule A PUnit.{1}) :
    ι A PUnit.{1} M N PUnit.unit ≫ (ringIso A M N).hom = 𝟙 _ :=
  ι_desc A PUnit.{1} M N (ringFamily A M N) PUnit.unit

lemma ringIso_hom_element (M : RightModule A PUnit.{1}) (N : LeftModule A PUnit.{1})
    {r s n : ℤ} (m : (M.obj (op PUnit.unit)).X r) (v : (N.obj PUnit.unit).X s)
    (hn : r + s = n) :
    (ringIso A M N).hom.f n (element A PUnit.{1} M N PUnit.unit m v hn) =
      ιTensorObj (M.obj (op PUnit.unit)) (N.obj PUnit.unit) r s n hn (m ⊗ₜ[A] v) := by
  exact congrArg (fun f => f.f n
    (ιTensorObj (M.obj (op PUnit.unit)) (N.obj PUnit.unit) r s n hn (m ⊗ₜ[A] v)))
    (ι_ringIso_hom A M N)

@[reassoc]
lemma ringIso_naturality {M M' : ModuleCategory A PUnit.{1}}
    {N N' : LeftModuleCategory A PUnit.{1}} (f : M ⟶ M') (g : N ⟶ N') :
    map A PUnit.{1} f g ≫
      (ringIso A (ForgetEnrichment.to (Complex A) M') (ForgetEnrichment.to (Complex A) N')).hom =
    (ringIso A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N)).hom ≫
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map f ⊗ₘ
        (leftModuleEvaluation A PUnit.{1} PUnit.unit).map g) := by
  apply (cancel_epi (ringIso A (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)).inv).mp
  change ι A PUnit.{1} (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) PUnit.unit ≫ map A PUnit.{1} f g ≫
        (ringIso A (ForgetEnrichment.to (Complex A) M')
          (ForgetEnrichment.to (Complex A) N')).hom =
    ι A PUnit.{1} (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) PUnit.unit ≫
        (ringIso A (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) N)).hom ≫ _
  rw [ι_map_assoc, ι_ringIso_hom, ι_ringIso_hom_assoc]
  let fx : (ForgetEnrichment.to (Complex A) M).obj (op PUnit.unit) ⟶
      (ForgetEnrichment.to (Complex A) M').obj (op PUnit.unit) :=
    (moduleEvaluation A PUnit.{1} PUnit.unit).map f
  let gx : (ForgetEnrichment.to (Complex A) N).obj PUnit.unit ⟶
      (ForgetEnrichment.to (Complex A) N').obj PUnit.unit :=
    (leftModuleEvaluation A PUnit.{1} PUnit.unit).map g
  change (fx ⊗ₘ gx) ≫ 𝟙 _ = fx ⊗ₘ gx
  exact Category.comp_id _

/-- 指定した非有界複体二つに対する既存cochainTensorとの比較。 -/
abbrev ringComplexTensorIso (P Q : Complex A) :
    obj A PUnit.{1} (ringModule A P) (ringLeftModule A Q) ≅
      SerrePositivity.cochainTensor P Q := ringIso A (ringModule A P) (ringLeftModule A Q)

end SerrePositivity.DifferentialGraded.BalancedTensor
