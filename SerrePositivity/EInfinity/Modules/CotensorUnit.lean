module

public import SerrePositivity.EInfinity.Modules.CotensorPointwise
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Module.Graded

/-!
# 単位係数 cotensor の全次数評価

概要：M10 の単位係数 cotensor を元の加群へ同定するための評価を構成する。
方針：単位複体の唯一の生成元で内部 Hom を評価する。
規約：HA §4.2.1、閉零射だけでなく全 dg Hom 作用を照合する。
使われ方：同じ simplicial frame の元の加群からの coaugmentation。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 概要：単位からの次数付き Hom は唯一の生成元の像と線形同値。
方針：single 複体からの cochain の既存の同値を使う。
規約：HA §4.2.1、全整数次数。使われ方：単位 cotensor の同型。 -/
def cotensorUnitDegreeEquiv (K : Complex A) (p : ℤ) :
    (homComplex A (𝟙_ (Complex A)) K).X p ≃ₗ[A] K.X p where
  toEquiv := (Cochain.fromSingleEquiv (X := 𝟙_ (ModuleCat A)) (K := K)
    (zero_add p)).toEquiv.trans (moduleElementEquiv A (K.X p))
  map_add' z t := by
    change (Cochain.fromSingleEquiv (zero_add p) (z + t)) (1 : A) = _
    rw [map_add]
    rfl
  map_smul' r z := by
    change (Cochain.fromSingleEquiv (zero_add p) (r • z)) (1 : A) = _
    rw [Cochain.fromSingleEquiv_smul]
    rfl

/-- 概要：生成元での評価は内部 Hom 微分と可換し、複体の同型になる。
方針：single からの cochain 微分の公式を使う。
規約：HA §4.2.1、元の単位複体。使われ方：加群の単位則。 -/
def cotensorUnitComplexIso (K : Complex A) :
    homComplex A (𝟙_ (Complex A)) K ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (cotensorUnitDegreeEquiv A K p).toModuleIso) (by
      intro p q hpq
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z p (zero_add p)
      change K.d p q ((Cochain.fromSingleEquiv (zero_add p)
        (Cochain.fromSingleMk f (zero_add p))) (1 : A)) =
        (Cochain.fromSingleEquiv (zero_add q)
          (δ p q (Cochain.fromSingleMk f (zero_add p)))) (1 : A)
      rw [Cochain.δ_fromSingleMk f (zero_add p) q q (zero_add q),
        Cochain.fromSingleEquiv_fromSingleMk, Cochain.fromSingleEquiv_fromSingleMk]
      rfl)

/-- 概要：単位での評価は同じ全 dg Hom 作用と可換。
方針：全次数の cochain 合成を唯一の生成元で評価する。
規約：HA §4.2.1、通常の自然性に制限しない。使われ方：主 Hom end への単位比較。 -/
lemma cotensorUnitComplexIso_naturality (P Q : Complex A) :
    (homCovariantDG A (𝟙_ (Complex A))).map P Q ≫
        homPostcompose _ (cotensorUnitComplexIso A Q).hom =
      homPrecompose (cotensorUnitComplexIso A P).hom Q := by
  apply chain_ext_apply
  intro p g
  apply Cochain.ext
  intro q r hqr
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change ((((homCovariantDG A (𝟙_ (Complex A))).map P Q).f p g).comp
      (Cochain.ofHom (cotensorUnitComplexIso A Q).hom) (add_zero p)).v q r hqr z =
    ((Cochain.ofHom (cotensorUnitComplexIso A P).hom).comp g (zero_add p)).v q r hqr z
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v]
  change (cotensorUnitComplexIso A Q).hom.f r
      ((((homCovariantDG A (𝟙_ (Complex A))).map P Q).f p g).v q r hqr z) =
    g.v q r hqr ((cotensorUnitComplexIso A P).hom.f q z)
  rw [homCovariantDG_map_element]
  change (((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv ≫
    (z.comp g hqr).v 0 r (zero_add r)) (1 : A)) = _
  rw [Cochain.comp_v z g hqr 0 q r (zero_add q) hqr]
  rfl

/-- 概要：同じ単位評価は元の通常射の後合成にも自然。
方針：全次数の cochain 合成を生成元で評価する。
規約：HA §4.2.1、同じ後合成。使われ方：全加群族の単位則。 -/
lemma cotensorUnitComplexIso_postcompose {P Q : Complex A} (f : P ⟶ Q) :
    homPostcompose (𝟙_ (Complex A)) f ≫ (cotensorUnitComplexIso A Q).hom =
      (cotensorUnitComplexIso A P).hom ≫ f := by
  apply chain_ext_apply
  intro p z
  change (((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv ≫
    (z.comp (Cochain.ofHom f) (add_zero p)).v 0 p (zero_add p)) (1 : A)) = _
  rw [Cochain.comp_v z (Cochain.ofHom f) (add_zero p) 0 p p (zero_add p) (add_zero p),
    Cochain.ofHom_v]
  rfl

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：同じ単位 cotensor は元の加群そのものと同型。
方針：全次数自然な複体同型を既存の主 Hom end へ持ち上げる。
規約：HA §4.2.1、閉零射だけで代用しない。使われ方：frame の元の始域。 -/
def moduleCotensorUnitIsoObj (M : ModuleCategory A D) :
    moduleCotensor A D (𝟙_ (Complex A)) M ≅ M :=
  moduleIsoMk A D
    (M := dgModuleCotensor A D (𝟙_ (Complex A)) (ForgetEnrichment.to (Complex A) M))
    (N := ForgetEnrichment.to (Complex A) M)
    (fun x => cotensorUnitComplexIso A ((ForgetEnrichment.to (Complex A) M).obj x)) (by
      intro x y
      change ((ForgetEnrichment.to (Complex A) M).map x y ≫
        (homCovariantDG A (𝟙_ (Complex A))).map _ _) ≫ _ =
        (ForgetEnrichment.to (Complex A) M).map x y ≫ _
      exact (Category.assoc _ _ _).trans
        (congrArg (fun z => (ForgetEnrichment.to (Complex A) M).map x y ≫ z)
          (cotensorUnitComplexIso_naturality A
            ((ForgetEnrichment.to (Complex A) M).obj x)
            ((ForgetEnrichment.to (Complex A) M).obj y))))

/-- 概要：元の加群同型の順射成分は同じ生成元評価。
方針：主 Hom end の同型の評価則を使う。
規約：HA §4.2.1、元の射。使われ方：全族の自然性の照合。 -/
lemma moduleCotensorUnitIsoObj_hom_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map (moduleCotensorUnitIsoObj A D M).hom =
      (cotensorUnitComplexIso A ((moduleEvaluation A D x).obj M)).hom :=
  moduleIsoMk_hom_eval A D _ _ x

/-- 概要：単位則は全ての元の加群射について同じ自然同型。
方針：元の後合成の評価則を各対象で使う。
規約：HA §4.2.1、全標的。使われ方：自然な coaugmentation の始域同定。 -/
def moduleCotensorUnitIso : moduleCotensorFunctor A D (𝟙_ (Complex A)) ≅
    𝟭 (ModuleCategory A D) :=
  NatIso.ofComponents (moduleCotensorUnitIsoObj A D) (by
    intro M N f
    apply moduleMorphism_ext
    intro x
    change (moduleEvaluation A D x).map
        (moduleCotensorMap A D (𝟙_ (Complex A)) f ≫ (moduleCotensorUnitIsoObj A D N).hom) =
      (moduleEvaluation A D x).map ((moduleCotensorUnitIsoObj A D M).hom ≫ f)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      moduleCotensorMap_eval, moduleCotensorUnitIsoObj_hom_eval,
      moduleCotensorUnitIsoObj_hom_eval]
    exact cotensorUnitComplexIso_postcompose A ((moduleEvaluation A D x).map f))

end SerrePositivity.EInfinity.Modules
