module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLengthAction
public import SerrePositivity.DifferentialGraded.Quotient.Category
public import SerrePositivity.DifferentialGraded.Module.Restriction
public import SerrePositivity.DifferentialGraded.Module.Action
public import SerrePositivity.DifferentialGraded.Module.ActionChain
public import SerrePositivity.DifferentialGraded.Functor.Opposite

/-! # 商の代表加群の長さ部分加群

元の dg 圏へ制限した代表加群への包含で全次数作用の単位・合成を検証する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 先頭作用は商の合成を元の Hom に制限したもの。 -/
lemma quotientPrepend_composition (S : Set D) (x y z : D) :
    quotientPrepend A D S x y z =
      (originalHomInclusion A D S x y ▷ quotientHom A D S y z) ≫
        quotientComposition A D S x y z := by
  apply tensorHom_ext
  intro p q r hr
  rw [HomologicalComplex.comp_f, ← Category.assoc, ι_whiskerRight,
    Category.assoc, quotientComposition_ι, quotientPrepend_ι]
  rw [internalPrepend, HomologicalComplex.comp_f, ← Category.assoc, ι_whiskerRight]
  rfl

/-- 商の代表加群を元の dg 圏へ制限する。 -/
abbrev quotientRepresentableRestriction (S : Set D) (z : D) : RightModule A D :=
  restrictModule A D (QuotientObject D S) (inclusion A D S).op (representable A ⟨z⟩)

lemma quotientRepresentableRestriction_action (S : Set D) (z : D) (x y : Dᵒᵖ) :
    moduleActionChain A (quotientRepresentableRestriction A D S z) x y =
      quotientPrepend A D S y.unop x.unop z := by
  change uncurryRight (originalHomInclusion A D S y.unop x.unop ≫
    curryRight (quotientComposition A D S y.unop x.unop z)) = _
  rw [← curryRight_naturality_source, uncurryRight_curryRight]
  exact (quotientPrepend_composition A D S y.unop x.unop z).symm

/-- 長さ部分複体の全 Hom chain map。 -/
def lengthModuleMap (S : Set D) (z : D) (n : ℕ) (x y : Dᵒᵖ) :
    (x ⟶[Complex A] y) ⟶
      homComplex A (lengthComplex A D S x.unop z n) (lengthComplex A D S y.unop z n) :=
  curryRight (lengthPrepend A D S y.unop x.unop z n)

lemma lengthModuleMap_inclusion (S : Set D) (z : D) (n : ℕ) (x y : Dᵒᵖ) :
    lengthModuleMap A D S z n x y ≫
        homPostcompose (lengthComplex A D S x.unop z n) (lengthInclusion A D S y.unop z n) =
      (quotientRepresentableRestriction A D S z).map x y ≫
        homPrecompose (lengthInclusion A D S x.unop z n) (quotientHom A D S y.unop z) := by
  rw [lengthModuleMap, ← curryRight_naturality_target, lengthPrepend_inclusion]
  change curryRight ((𝟙 (homObject A D y.unop x.unop) ⊗ₘ
    lengthInclusion A D S x.unop z n) ≫ quotientPrepend A D S y.unop x.unop z) = _
  rw [curryRight_naturality_domain, ← quotientRepresentableRestriction_action,
    curryRight_uncurryRight]

lemma lengthModuleMap_inclusion_v (S : Set D) (z : D) (n : ℕ) (x y : Dᵒᵖ)
    (p i j : ℤ) (hij : i + p = j) (f : GradedHom A x y p)
    (t : (lengthComplex A D S x.unop z n).X i) :
    (lengthInclusion A D S y.unop z n).f j
        (((lengthModuleMap A D S z n x y).f p f).v i j hij t) =
      moduleAction A (quotientRepresentableRestriction A D S z) f
        ((lengthInclusion A D S x.unop z n).f i t) hij := by
  have h := congrArg (fun g => g.f p f) (lengthModuleMap_inclusion A D S z n x y)
  change (((lengthModuleMap A D S z n x y).f p f).comp
      (Cochain.ofHom (lengthInclusion A D S y.unop z n)) (add_zero p)) =
    (Cochain.ofHom (lengthInclusion A D S x.unop z n)).comp
      (((quotientRepresentableRestriction A D S z).map x y).f p f) (zero_add p) at h
  have hv := congrArg (fun c => c.v i j hij t) h
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, ModuleCat.comp_apply] at hv
  exact hv

lemma lengthModuleMap_id (S : Set D) (z : D) (n : ℕ) (x : Dᵒᵖ) :
    eId (Complex A) x ≫ lengthModuleMap A D S z n x x =
      identity (lengthComplex A D S x.unop z n) := by
  apply (unitCycleEquiv (homComplex A (lengthComplex A D S x.unop z n)
    (lengthComplex A D S x.unop z n))).injective
  apply Subtype.ext
  change (cycleFromUnit _ (eId (Complex A) x ≫ lengthModuleMap A D S z n x x)).val =
    (cycleFromUnit _ (identity (lengthComplex A D S x.unop z n))).val
  rw [cycleFromUnit_postcomp, identity, cycleFromUnit_unitFromCycle]
  change (lengthModuleMap A D S z n x x).f 0 (unitElement A x).val =
    Cochain.ofHom (𝟙 (lengthComplex A D S x.unop z n))
  apply Cochain.ext₀
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply Subtype.ext
  change (lengthInclusion A D S x.unop z n).f i
    (((lengthModuleMap A D S z n x x).f 0 (unitElement A x).val).v i i (add_zero i) t) =
      (lengthInclusion A D S x.unop z n).f i t
  rw [lengthModuleMap_inclusion_v]
  exact moduleAction_unit A (quotientRepresentableRestriction A D S z) x i _

lemma lengthModuleMap_comp (S : Set D) (t : D) (n : ℕ) (x y z : Dᵒᵖ) :
    eComp (Complex A) x y z ≫ lengthModuleMap A D S t n x z =
      (lengthModuleMap A D S t n x y ⊗ₘ lengthModuleMap A D S t n y z) ≫
        enrichedComposition _ _ _ := by
  apply tensorHom_ext
  intro p q m hm
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change (lengthModuleMap A D S t n x z).f m (forward A f g hm) =
    (enrichedComposition _ _ _).f m
      ((lengthModuleMap A D S t n x y ⊗ₘ lengthModuleMap A D S t n y z).f m
        (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q m hm (f ⊗ₜ[A] g)))
  rw [tensorMap_apply, enrichedComposition_apply]
  apply Cochain.ext
  intro i j hij
  rw [Cochain.units_smul_v, Cochain.comp_v _ _ hm i (i + p) j rfl (by omega)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change (lengthInclusion A D S z.unop t n).f j
      (((lengthModuleMap A D S t n x z).f m (forward A f g hm)).v i j hij a) =
    (lengthInclusion A D S z.unop t n).f j
      ((p * q).negOnePow • (((lengthModuleMap A D S t n y z).f q g).v (i + p) j (by omega)
        (((lengthModuleMap A D S t n x y).f p f).v i (i + p) rfl a)))
  rw [lengthModuleMap_inclusion_v, chain_units_smul,
    lengthModuleMap_inclusion_v, lengthModuleMap_inclusion_v]
  exact moduleAction_forward A (quotientRepresentableRestriction A D S t) f g
    ((lengthInclusion A D S x.unop t n).f i a) hm rfl hij

/-- 長さ n 以下の商 path からなる実際の右 dg 加群。 -/
abbrev lengthModule (S : Set D) (z : D) (n : ℕ) : RightModule A D where
  obj x := lengthComplex A D S x.unop z n
  map := lengthModuleMap A D S z n
  map_id := lengthModuleMap_id A D S z n
  map_comp := lengthModuleMap_comp A D S z n

/-- 長さ部分加群から制限代表加群への実際の閉零射。 -/
def lengthModuleInclusion (S : Set D) (z : D) (n : ℕ) :
    ForgetEnrichment.of (Complex A) (lengthModule A D S z n) ⟶
      ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z) :=
  moduleMorphismMk A D (fun x => lengthInclusion A D S x.unop z n)
    (lengthModuleMap_inclusion A D S z n)

@[simp] lemma lengthModuleInclusion_eval (S : Set D) (z : D) (n : ℕ) (x : D) :
    (moduleEvaluation A D x).map (lengthModuleInclusion A D S z n) =
      lengthInclusion A D S x z n := moduleMorphismMk_eval A D _ _ x

instance lengthModuleInclusion_mono (S : Set D) (z : D) (n : ℕ) :
    Mono (lengthModuleInclusion A D S z n) where
  right_cancellation {Z} f g h := by
    apply moduleMorphism_ext
    intro x
    apply (cancel_mono (lengthInclusion A D S x z n)).mp
    have hx := congrArg (fun k => (moduleEvaluation A D x).map k) h
    simpa only [CategoryTheory.Functor.map_comp, lengthModuleInclusion_eval] using hx

lemma lengthModuleMap_transition (S : Set D) (z : D) {m n : ℕ} (hmn : m ≤ n)
    (x y : Dᵒᵖ) :
    lengthModuleMap A D S z m x y ≫
        homPostcompose (lengthComplex A D S x.unop z m) (lengthMap A D S y.unop z hmn) =
      lengthModuleMap A D S z n x y ≫
        homPrecompose (lengthMap A D S x.unop z hmn) (lengthComplex A D S y.unop z n) := by
  rw [lengthModuleMap, ← curryRight_naturality_target, lengthPrepend_map]
  change curryRight ((𝟙 (homObject A D y.unop x.unop) ⊗ₘ
    lengthMap A D S x.unop z hmn) ≫ lengthPrepend A D S y.unop x.unop z n) = _
  rw [curryRight_naturality_domain]
  rfl

/-- 長さを増やす実際の右 dg 加群射。 -/
def lengthModuleTransition (S : Set D) (z : D) {m n : ℕ} (hmn : m ≤ n) :
    ForgetEnrichment.of (Complex A) (lengthModule A D S z m) ⟶
      ForgetEnrichment.of (Complex A) (lengthModule A D S z n) :=
  moduleMorphismMk A D (fun x => lengthMap A D S x.unop z hmn)
    (lengthModuleMap_transition A D S z hmn)

@[simp] lemma lengthModuleTransition_eval (S : Set D) (z : D) {m n : ℕ}
    (hmn : m ≤ n) (x : D) :
    (moduleEvaluation A D x).map (lengthModuleTransition A D S z hmn) =
      lengthMap A D S x z hmn := moduleMorphismMk_eval A D _ _ x

@[reassoc] lemma lengthModuleTransition_inclusion (S : Set D) (z : D) {m n : ℕ}
    (hmn : m ≤ n) :
    lengthModuleTransition A D S z hmn ≫ lengthModuleInclusion A D S z n =
      lengthModuleInclusion A D S z m := by
  apply moduleMorphism_ext
  intro x
  simp only [CategoryTheory.Functor.map_comp, lengthModuleTransition_eval,
    lengthModuleInclusion_eval, lengthMap_inclusion]

/-- 長さ filtration を右 dg 加群圏内の厳密な ℕ 図式にする。 -/
def lengthModuleDiagram (S : Set D) (z : D) : ℕ ⥤ ModuleCategory A D where
  obj n := ForgetEnrichment.of (Complex A) (lengthModule A D S z n)
  map f := lengthModuleTransition A D S z (leOfHom f)
  map_id n := by
    apply moduleMorphism_ext
    intro x
    simp only [lengthModuleTransition_eval, CategoryTheory.Functor.map_id, lengthMap_refl]
    rfl
  map_comp f g := by
    apply moduleMorphism_ext
    intro x
    simp only [lengthModuleTransition_eval, CategoryTheory.Functor.map_comp, lengthMap_comp]

/-- 制限代表加群は長さ filtration の cocone。 -/
def lengthModuleCocone (S : Set D) (z : D) : Cocone (lengthModuleDiagram A D S z) where
  pt := ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z)
  ι.app := lengthModuleInclusion A D S z
  ι.naturality {m n} f := by
    change lengthModuleTransition A D S z (leOfHom f) ≫ lengthModuleInclusion A D S z n =
      lengthModuleInclusion A D S z m ≫ 𝟙 _
    rw [lengthModuleTransition_inclusion, Category.comp_id]

end SerrePositivity.DifferentialGraded.DGQuotient
