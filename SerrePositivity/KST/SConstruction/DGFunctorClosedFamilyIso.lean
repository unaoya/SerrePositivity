module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorEnrichment
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorClosedComparison

/-! # 全 Hom 自然な指定同型族と実 dg 関手圏の閉同型
概要：元の全次数自然な同型族を、元の Hom end を持つ dg 関手圏の閉同型にする。
方針：単位パラメータの普遍性で順逆射を作り、全対象評価で逆律を検査する。
規約：通常の自然同型だけを入力にしない。使われ方：実 Perf 延長の入力同型の作用。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] (F G : DGFunctor R D E)

/-- 元の全 Hom 自然な閉射族を、同じ全次数 Hom end 内の閉射にする。 -/
def dgFunctorClosedHomFromFamily
    (a : ∀ x : D, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
      ForgetEnrichment.of (Complex R) (G.obj x))
    (h : ∀ x y : D, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y))) :
    ForgetEnrichment.of (Complex R) F ⟶ ForgetEnrichment.of (Complex R) G :=
  (dgFunctorHomEquiv R D E (𝟙_ (Complex R)) F G).symm (dgFunctorClosedComparison R F G a h)

/-- 同じ Hom end 内の閉射の評価は、元の同じ閉射族を回収する。 -/
lemma dgFunctorClosedHomFromFamily_eval (a) (h) (x : D) :
    (dgFunctorEvaluationDG R D E x).onClosed.map
      (dgFunctorClosedHomFromFamily R D E F G a h) = a x := by
  apply (eHomEquiv (Complex R)).injective
  change (dgFunctorHomEquiv R D E (𝟙_ (Complex R)) F G).symm
      (dgFunctorClosedComparison R F G a h) ≫ dgFunctorHomπ R D E F G x = _
  exact dgFunctorHomEquiv_symm_π R D E _ F G (dgFunctorClosedComparison R F G a h) x

/-- 元の dg 関手圏の閉射は、全対象の同じ閉評価で判定できる。 -/
lemma dgFunctorClosedHom_ext
    {f g : ForgetEnrichment.of (Complex R) F ⟶ ForgetEnrichment.of (Complex R) G}
    (h : ∀ x : D, (dgFunctorEvaluationDG R D E x).onClosed.map f =
      (dgFunctorEvaluationDG R D E x).onClosed.map g) : f = g := by
  apply (eHomEquiv (Complex R)).injective
  apply dgFunctorHom_ext R D E
  intro x
  have hx := congrArg (ForgetEnrichment.homTo (Complex R)) (h x)
  change ForgetEnrichment.homTo (Complex R) f ≫ dgFunctorHomπ R D E F G x =
    ForgetEnrichment.homTo (Complex R) g ≫ dgFunctorHomπ R D E F G x at hx
  exact hx

/-- 元の全 Hom 自然な指定同型族を、同じ実 dg 関手圏の閉同型として保持する。 -/
def dgFunctorClosedIsoFromFamily
    (e : ∀ x : D, ForgetEnrichment.of (Complex R) (F.obj x) ≅
      ForgetEnrichment.of (Complex R) (G.obj x))
    (h : ∀ x y : D, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (e y).hom =
      G.map x y ≫ eHomWhiskerRight (Complex R) (e x).hom
        (ForgetEnrichment.of (Complex R) (G.obj y))) :
    ForgetEnrichment.of (Complex R) F ≅ ForgetEnrichment.of (Complex R) G where
  hom := dgFunctorClosedHomFromFamily R D E F G (fun x => (e x).hom) h
  inv := dgFunctorClosedHomFromFamily R D E G F (fun x => (e x).inv)
    (dgFunctorClosedComparison_inv_naturality R F G e h)
  hom_inv_id := by
    apply dgFunctorClosedHom_ext R D E
    intro x
    rw [CategoryTheory.Functor.map_comp, dgFunctorClosedHomFromFamily_eval,
      dgFunctorClosedHomFromFamily_eval,
      CategoryTheory.Functor.map_id]
    exact (e x).hom_inv_id
  inv_hom_id := by
    apply dgFunctorClosedHom_ext R D E
    intro x
    rw [CategoryTheory.Functor.map_comp, dgFunctorClosedHomFromFamily_eval,
      dgFunctorClosedHomFromFamily_eval,
      CategoryTheory.Functor.map_id]
    exact (e x).inv_hom_id

end SerrePositivity.KST.SConstruction
