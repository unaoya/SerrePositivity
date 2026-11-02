module

public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration
public import SerrePositivity.DifferentialGraded.Quotient.Composition
public import SerrePositivity.DifferentialGraded.Module.Restriction
public import SerrePositivity.DifferentialGraded.Module.Action
public import SerrePositivity.DifferentialGraded.Module.ActionChain
public import SerrePositivity.DifferentialGraded.Functor.Opposite
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects
public import SerrePositivity.DifferentialGraded.Module.ConeFunctor
public import SerrePositivity.DifferentialGraded.Complexes.ConeElements
public import SerrePositivity.DifferentialGraded.Complexes.ConeGradedSplit

/-!
# Quotient.DerivedComparison.ColimitCones

## 概要
長さ部分加群の余極限と比較 cone の図式をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## DerivedComparisonLengthModule（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonLengthModule.lean） -/

/-! # 商の代表加群の長さ部分加群

元の dg 圏へ制限した代表加群への包含で全次数作用の単位・合成を検証する。
-/

@[expose] public section DerivedComparisonLengthModule
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end DerivedComparisonLengthModule

/-! ## DerivedComparisonModuleColimit（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonModuleColimit.lean） -/

/-! # 制限代表加群を長さ部分加群の逐次余極限として復元する -/

@[expose] public section DerivedComparisonModuleColimit
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 加群の長さ図式を評価すると Hom の長さ図式になる。 -/
def lengthModuleDiagramEvaluationIso (S : Set D) (z x : D) :
    lengthModuleDiagram A D S z ⋙ moduleEvaluation A D x ≅ lengthDiagram A D S x z :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro m n f
    change (moduleEvaluation A D x).map (lengthModuleTransition A D S z (leOfHom f)) ≫
      𝟙 _ = 𝟙 _ ≫ lengthMap A D S x z (leOfHom f)
    rw [Category.comp_id, Category.id_comp, lengthModuleTransition_eval])

def lengthModuleCoconeEvaluationIso (S : Set D) (z x : D) :
    (Cocone.precompose (lengthModuleDiagramEvaluationIso A D S z x).hom).obj
        (lengthCocone A D S x z) ≅
      (moduleEvaluation A D x).mapCocone (lengthModuleCocone A D S z) :=
  Cocone.ext (Iso.refl _) (by
    intro n
    change (𝟙 _ ≫ lengthInclusion A D S x z n) ≫ 𝟙 _ =
      (moduleEvaluation A D x).map (lengthModuleInclusion A D S z n)
    rw [Category.id_comp, Category.comp_id, lengthModuleInclusion_eval])

def lengthModuleCocone_eval_isColimit (S : Set D) (z x : D) :
    IsColimit ((moduleEvaluation A D x).mapCocone (lengthModuleCocone A D S z)) :=
  IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (lengthModuleDiagramEvaluationIso A D S z x)
      (lengthCocone A D S x z)).symm (lengthCocone_isColimit A D S x z))
    (lengthModuleCoconeEvaluationIso A D S z x)

/-- 商の制限代表加群は、全長さ部分加群の加群圏内での余極限である。 -/
def lengthModuleCocone_isColimit (S : Set D) (z : D) :
    IsColimit (lengthModuleCocone A D S z) :=
  moduleIsColimitOfEvaluations A D _ (lengthModuleCocone_eval_isColimit A D S z)

instance lengthModuleDiagram_hasColimit (S : Set D) (z : D) :
    HasColimit (lengthModuleDiagram A D S z) :=
  HasColimit.mk ⟨_, lengthModuleCocone_isColimit A D S z⟩

def lengthModuleColimitIso (S : Set D) (z : D) :
    colimit (lengthModuleDiagram A D S z) ≅
      ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D S z) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (lengthModuleCocone_isColimit A D S z)

@[reassoc] lemma lengthModuleColimitIso_ι (S : Set D) (z : D) (n : ℕ) :
    colimit.ι (lengthModuleDiagram A D S z) n ≫ (lengthModuleColimitIso A D S z).hom =
      lengthModuleInclusion A D S z n :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ n

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonModuleColimit

/-! ## DerivedComparisonConeDiagram（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonConeDiagram.lean） -/

/-! # 長さ零段階からの比較 cone の厳密な図式 -/

@[expose] public section DerivedComparisonConeDiagram
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

lemma complexConeMap_fst {P Q R T : Complex A} (f : P ⟶ Q) (g : R ⟶ T)
    (a : P ⟶ R) (b : Q ⟶ T) (h : f ≫ b = a ≫ g) (i : ℤ) :
    (mappingCone.map f g a b h).f i ≫ (mappingCone.fst g).val.v i (i + 1) rfl =
      (mappingCone.fst f).val.v i (i + 1) rfl ≫ a.f (i + 1) := by
  change (Cochain.ofHom (mappingCone.map f g a b h)).v i i (add_zero i) ≫ _ = _
  rw [coneMapCochain_ofHom, coneMapCochain_fst_v]
  simp only [Int.negOnePow_zero, one_smul, Cochain.ofHom_v]

lemma complexConeMap_snd {P Q R T : Complex A} (f : P ⟶ Q) (g : R ⟶ T)
    (a : P ⟶ R) (b : Q ⟶ T) (h : f ≫ b = a ≫ g) (i : ℤ) :
    (mappingCone.map f g a b h).f i ≫ (mappingCone.snd g).v i i (add_zero i) =
      (mappingCone.snd f).v i i (add_zero i) ≫ b.f i := by
  change (Cochain.ofHom (mappingCone.map f g a b h)).v i i (add_zero i) ≫ _ = _
  rw [coneMapCochain_ofHom, coneMapCochain_snd_v, Cochain.ofHom_v]

lemma complexConeMap_f_injective {P Q R T : Complex A} (f : P ⟶ Q) (g : R ⟶ T)
    (a : P ⟶ R) (b : Q ⟶ T) (h : f ≫ b = a ≫ g) (i : ℤ)
    (ha : Function.Injective (a.f (i + 1))) (hb : Function.Injective (b.f i)) :
    Function.Injective ((mappingCone.map f g a b h).f i) := by
  intro t s hts
  apply complexConeElement_ext A f i
  · apply ha
    have he := congrArg (fun z => (mappingCone.fst g).val.v i (i + 1) rfl z) hts
    simpa only [← ModuleCat.comp_apply, complexConeMap_fst] using he
  · apply hb
    have he := congrArg (fun z => (mappingCone.snd g).v i i (add_zero i) z) hts
    simpa only [← ModuleCat.comp_apply, complexConeMap_snd] using he

lemma complexConeMap_elementMk {P Q R T : Complex A} (f : P ⟶ Q) (g : R ⟶ T)
    (a : P ⟶ R) (b : Q ⟶ T) (h : f ≫ b = a ≫ g) (i : ℤ)
    (t : P.X (i + 1)) (s : Q.X i) :
    (mappingCone.map f g a b h).f i (complexConeElementMk A f i t s) =
      complexConeElementMk A g i (a.f (i + 1) t) (b.f i s) := by
  apply complexConeElement_ext A g i
  · rw [← ModuleCat.comp_apply, complexConeMap_fst, ModuleCat.comp_apply,
      complexConeElementMk_fst, complexConeElementMk_fst]
  · rw [← ModuleCat.comp_apply, complexConeMap_snd, ModuleCat.comp_apply,
      complexConeElementMk_snd, complexConeElementMk_snd]

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- ℕ 図式の零段階から各段階へ向かう射を arrow 圏内の図式にする。 -/
def zeroSourceArrowDiagram (F : ℕ ⥤ ModuleCategory A D) :
    ℕ ⥤ Arrow (ModuleCategory A D) where
  obj n := Arrow.mk (F.map (homOfLE (Nat.zero_le n)))
  map {m n} f := Arrow.homMk (𝟙 _) (F.map f) (by
    change 𝟙 _ ≫ F.map (homOfLE (Nat.zero_le n)) =
      F.map (homOfLE (Nat.zero_le m)) ≫ F.map f
    rw [Category.id_comp, ← CategoryTheory.Functor.map_comp]
    congr 1)
  map_id n := Arrow.hom_ext _ _ (by simp) (by simp)
  map_comp f g := Arrow.hom_ext _ _ (by simp) (by simp)

def zeroSourceArrowCocone (F : ℕ ⥤ ModuleCategory A D) (s : Cocone F) :
    Cocone (zeroSourceArrowDiagram A D F) where
  pt := Arrow.mk (s.ι.app 0)
  ι.app n := Arrow.homMk (𝟙 _) (s.ι.app n) (by
    change 𝟙 _ ≫ s.ι.app 0 = F.map (homOfLE (Nat.zero_le n)) ≫ s.ι.app n
    rw [Category.id_comp, s.w])
  ι.naturality {m n} f := by
    apply Arrow.hom_ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
      rfl
    · change F.map f ≫ s.ι.app n = s.ι.app m ≫ 𝟙 _
      rw [Category.comp_id, s.w]

/-- 有限長の比較 cone からなる実際の加群図式。 -/
def lengthComparisonConeDiagram (S : Set D) (z : D) : ℕ ⥤ ModuleCategory A D :=
  zeroSourceArrowDiagram A D (lengthModuleDiagram A D S z) ⋙ moduleConeFunctor A D

/-- 商全体への比較 cone を頂点とする cocone。 -/
def lengthComparisonConeCocone (S : Set D) (z : D) :
    Cocone (lengthComparisonConeDiagram A D S z) :=
  (moduleConeFunctor A D).mapCocone
    (zeroSourceArrowCocone A D (lengthModuleDiagram A D S z) (lengthModuleCocone A D S z))

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonConeDiagram

/-! ## DerivedComparisonConeColimit（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonConeColimit.lean） -/

/-! # 全体への比較 cone は有限長比較 cone の逐次余極限

各次数の cone の二成分と、商 Hom の有限長支持を使う。
-/

@[expose] public section DerivedComparisonConeColimit
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma lengthComparisonConeCocone_ι_eval (S : Set D) (z : D) (n : ℕ) (x : D) :
    (moduleEvaluation A D x).map ((lengthComparisonConeCocone A D S z).ι.app n) =
      mappingCone.map
        ((moduleEvaluation A D x).map (lengthModuleTransition A D S z (Nat.zero_le n)))
        ((moduleEvaluation A D x).map (lengthModuleInclusion A D S z 0))
        ((moduleEvaluation A D x).map (𝟙 _))
        ((moduleEvaluation A D x).map (lengthModuleInclusion A D S z n))
        (moduleSquare_eval A D _ _ _ _
          (by rw [lengthModuleTransition_inclusion, Category.id_comp]) x) := by
  change (moduleEvaluation A D x).map (moduleConeMap A D
    (lengthModuleTransition A D S z (Nat.zero_le n)) (lengthModuleInclusion A D S z 0)
      (𝟙 _) (lengthModuleInclusion A D S z n)
      (by rw [lengthModuleTransition_inclusion, Category.id_comp])) = _
  exact moduleConeMap_eval A D _ _ _ _ _ x

lemma lengthComparisonConeCocone_f_injective (S : Set D) (z : D) (n : ℕ)
    (x : D) (i : ℤ) :
    Function.Injective (((moduleEvaluation A D x).map
      ((lengthComparisonConeCocone A D S z).ι.app n)).f i) := by
  rw [lengthComparisonConeCocone_ι_eval]
  apply complexConeMap_f_injective A _ _ _ _ _ i
  · rw [CategoryTheory.Functor.map_id, HomologicalComplex.id_f]
    exact fun _ _ h => h
  · rw [lengthModuleInclusion_eval]
    exact Subtype.val_injective

/-- 全体 cone の各要素は、ある有限長比較 cone から来る。 -/
lemma lengthComparisonConeCocone_exists (S : Set D) (z x : D) (i : ℤ)
    (t : ((moduleEvaluation A D x).obj (lengthComparisonConeCocone A D S z).pt).X i) :
    ∃ (n : ℕ) (s : ((moduleEvaluation A D x).obj
      ((lengthComparisonConeDiagram A D S z).obj n)).X i),
      ((moduleEvaluation A D x).map ((lengthComparisonConeCocone A D S z).ι.app n)).f i s = t := by
  let g := (moduleEvaluation A D x).map (lengthModuleInclusion A D S z 0)
  let b : (internalHom A D S x z).X i := (mappingCone.snd g).v i i (add_zero i) t
  obtain ⟨n, hn⟩ := exists_lengthSubmodule A D S x z i b
  let f := (moduleEvaluation A D x).map (lengthModuleTransition A D S z (Nat.zero_le n))
  refine ⟨n, complexConeElementMk A f i ((mappingCone.fst g).val.v i (i + 1) rfl t)
    ⟨b, hn⟩, ?_⟩
  let a := (moduleEvaluation A D x).map
    (𝟙 (ForgetEnrichment.of (Complex A) (lengthModule A D S z 0)))
  let c := (moduleEvaluation A D x).map (lengthModuleInclusion A D S z n)
  have hcomm : f ≫ c = a ≫ g := moduleSquare_eval A D _ _ _ _
    (by rw [lengthModuleTransition_inclusion, Category.id_comp]) x
  have hm := complexConeMap_elementMk A f g a c hcomm i
    ((mappingCone.fst g).val.v i (i + 1) rfl t) ⟨b, hn⟩
  have ha : a.f (i + 1) ((mappingCone.fst g).val.v i (i + 1) rfl t) =
      (mappingCone.fst g).val.v i (i + 1) rfl t := by
    dsimp only [a]
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.id_apply]
  have hc : c.f i ⟨b, hn⟩ = b := by
    dsimp only [c]
    rw [lengthModuleInclusion_eval]
    rfl
  have he : complexConeElementMk A g i
      (a.f (i + 1) ((mappingCone.fst g).val.v i (i + 1) rfl t)) (c.f i ⟨b, hn⟩) = t := by
    rw [ha, hc]
    exact complexConeElementMk_eta A g i t
  rw [lengthComparisonConeCocone_ι_eval]
  exact hm.trans he

def lengthComparisonConeCocone_degree_isColimit (S : Set D) (z x : D) (i : ℤ) :
    IsColimit
      ((moduleEvaluation A D x ⋙ HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i).mapCocone
        (lengthComparisonConeCocone A D S z)) := by
  have : ReflectsFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    reflectsSmallestFilteredColimits_of_reflectsFilteredColimits (forget (ModuleCat.{u} A))
  apply isColimitOfReflects (forget (ModuleCat.{u} A))
  apply Types.FilteredColimit.isColimitOf'
  · intro t
    obtain ⟨n, s, hs⟩ := lengthComparisonConeCocone_exists A D S z x i t
    exact ⟨n, s, hs.symm⟩
  · intro n t s h
    have he := lengthComparisonConeCocone_f_injective A D S z n x i h
    exact ⟨n, 𝟙 n, by rw [he]⟩

def lengthComparisonConeCocone_eval_isColimit (S : Set D) (z x : D) :
    IsColimit ((moduleEvaluation A D x).mapCocone (lengthComparisonConeCocone A D S z)) :=
  HomologicalComplex.isColimitOfEval _ _
    (lengthComparisonConeCocone_degree_isColimit A D S z x)

/-- 加群圏内での比較 cone の厳密な余極限性。 -/
def lengthComparisonConeCocone_isColimit (S : Set D) (z : D) :
    IsColimit (lengthComparisonConeCocone A D S z) :=
  moduleIsColimitOfEvaluations A D _ (lengthComparisonConeCocone_eval_isColimit A D S z)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonConeColimit
