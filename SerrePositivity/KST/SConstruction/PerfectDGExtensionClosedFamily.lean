module
public import SerrePositivity.KST.SConstruction.DGFunctorClosedFamilyIso
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionInputHom
public import SerrePositivity.KST.SConstruction.DGExtensionParameterPullback
public import SerrePositivity.KST.SConstruction.DGParameterUniversal
public import SerrePositivity.KST.SConstruction.DGClosedComparisonFromParameter
public import SerrePositivity.DifferentialGraded.Functor.DGClosedComparisonIso

/-! # 指定した全 Hom 自然同型族の実一回 Perf 延長
概要：元の入力同型を実入力 Hom へ入れ、同じ一回 Perf 延長の各実対象に作用させる。
方針：入力 Hom の単位・合成保存とパラメータ引き戻しを用い、同じ成分で自然性を回収する。
規約：全 Perf の Small 性も全体の Hom end も仮定しない。使われ方：元の cone 比較の実延長。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E]

/-- 各実 perfect 入力上で、元の入力 dg 関手圏から実延長像への同じ全 Hom 作用。 -/
def perfectDGExtensionInputFunctorAt (M : PerfectDGModule R D) :
    DGFunctor R (DGFunctor R D E) (PerfectDGModule R E) where
  obj F := (perfectDGExtension R D E F).obj M
  map F G := perfectDGExtensionInputHom R D E F G M
  map_id F := by
    change dgFunctorIdentity R D E F ≫ perfectDGExtensionInputHom R D E F F M = _
    rw [perfectDGExtensionInputHom_module]
    exact dgModuleExtensionInputHom_identity R D E F M.val
  map_comp F G H := perfectDGExtensionInputHom_composition R D E F G H M

/-- 任意の元のパラメータ作用は、同じ入力 Hom の普遍作用への前合成。 -/
lemma perfectDGExtensionInputHom_factorization {F G : DGFunctor R D E} {K : Complex R}
    (τ : DGFunctorParamTrans R D E K F G) (M : PerfectDGModule R D) :
    (dgFunctorHomEquiv R D E K F G).symm τ ≫ perfectDGExtensionInputHom R D E F G M =
      (perfectDGExtensionParameter R D E τ).app M := by
  have h := congrArg (fun σ => (perfectDGExtensionParameter R D E σ).app M)
    (dgParameterUniversal_pullback R D E F G τ)
  rw [perfectDGExtensionParameter_pullback] at h
  exact h

variable (F G : DGFunctor R D E)
  (e : ∀ x : D, ForgetEnrichment.of (Complex R) (F.obj x) ≅
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y : D, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (e y).hom =
    G.map x y ≫ eHomWhiskerRight (Complex R) (e x).hom
      (ForgetEnrichment.of (Complex R) (G.obj y)))

/-- 同じ元の入力同型の作用で得る、各実 perfect 入力の一回延長像の同型。 -/
def perfectDGExtensionClosedIsoFromFamilyAt (M : PerfectDGModule R D) :
    ForgetEnrichment.of (Complex R) ((perfectDGExtension R D E F).obj M) ≅
      ForgetEnrichment.of (Complex R) ((perfectDGExtension R D E G).obj M) :=
  (perfectDGExtensionInputFunctorAt R D E M).onClosed.mapIso
    (dgFunctorClosedIsoFromFamily R D E F G e h)

/-- 同じ延長像同型の順射は、元の同じ単位パラメータ延長の成分を回収する。 -/
lemma perfectDGExtensionClosedIsoFromFamilyAt_hom (M : PerfectDGModule R D) :
    ForgetEnrichment.homTo (Complex R)
      (perfectDGExtensionClosedIsoFromFamilyAt R D E F G e h M).hom =
      (perfectDGExtensionParameter R D E
        (dgFunctorClosedComparison R F G (fun x => (e x).hom) h)).app M := by
  change (dgFunctorHomEquiv R D E (𝟙_ (Complex R)) F G).symm
    (dgFunctorClosedComparison R F G (fun x => (e x).hom) h) ≫
      perfectDGExtensionInputHom R D E F G M = _
  exact perfectDGExtensionInputHom_factorization R D E _ M

/-- 同じ延長像同型の逆射も、元の同じ逆パラメータ延長の成分を回収する。 -/
lemma perfectDGExtensionClosedIsoFromFamilyAt_inv (M : PerfectDGModule R D) :
    ForgetEnrichment.homTo (Complex R)
      (perfectDGExtensionClosedIsoFromFamilyAt R D E F G e h M).inv =
      (perfectDGExtensionParameter R D E (dgFunctorClosedInverseComparison R F G e h)).app M := by
  change (dgFunctorHomEquiv R D E (𝟙_ (Complex R)) G F).symm
    (dgFunctorClosedInverseComparison R F G e h) ≫ perfectDGExtensionInputHom R D E G F M = _
  exact perfectDGExtensionInputHom_factorization R D E _ M

/-- 同じ元の延長像同型は、実 Perf 入力の全 Hom 複体に関して自然。 -/
lemma perfectDGExtensionClosedIsoFromFamilyAt_naturality (X Y : PerfectDGModule R D) :
    (perfectDGExtension R D E F).map X Y ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) ((perfectDGExtension R D E F).obj X))
      (perfectDGExtensionClosedIsoFromFamilyAt R D E F G e h Y).hom =
    (perfectDGExtension R D E G).map X Y ≫ eHomWhiskerRight (Complex R)
      (perfectDGExtensionClosedIsoFromFamilyAt R D E F G e h X).hom
      (ForgetEnrichment.of (Complex R) ((perfectDGExtension R D E G).obj Y)) :=
  dgClosedComparison_from_parameter R _ _
    (perfectDGExtensionParameter R D E (dgFunctorClosedComparison R F G (fun x => (e x).hom) h))
    (fun M => (perfectDGExtensionClosedIsoFromFamilyAt R D E F G e h M).hom)
    (fun M => (perfectDGExtensionClosedIsoFromFamilyAt_hom R D E F G e h M).symm) X Y

/-- 同じ元の全次数比較に由来する、一回 Perf 延長の閉零自然同型。 -/
def perfectDGExtensionClosedIsoFromFamily :
    (perfectDGExtension R D E F).onClosed ≅ (perfectDGExtension R D E G).onClosed :=
  dgFunctorClosedComparisonIso R _ _ (perfectDGExtensionClosedIsoFromFamilyAt R D E F G e h)
    (perfectDGExtensionClosedIsoFromFamilyAt_naturality R D E F G e h)

end SerrePositivity.KST.SConstruction
