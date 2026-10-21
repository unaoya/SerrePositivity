module
public import SerrePositivity.KST.SConstruction.DGStandardEnrichedFunctor
public import SerrePositivity.KST.SConstruction.DGClosedWhiskerComponents
public import SerrePositivity.InfinityCategories.Derived.AWClosedComposition

/-! # 全 Hom 閉零比較の標準 DK 豊穣自然変換
概要：元の全 Hom 上で自然な閉零射族を、標準 DK の豊穣自然変換へ移す。
方針：同じ閉零射の定数単体を使い、全成分の AW 前後合成を照合する。
規約：通常射だけの自然性や源の小ささを仮定しない。使われ方：Perf 作用の完全性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DoldKanComparison DGNerve.PinchedHom
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

/-- 元の閉零射の全定数単体を束ねる標準 Hom への単位射。 -/
def dgStandardClosedMap {x y : E}
    (a : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y) :
    𝟙_ SSet.{u} ⟶ standardHomSpace (R := A) x y where
  app n := ↾fun _ => standardConstant (closedHomEquiv A E _ _ a) n.unop.len
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (standardConstant_pullback (closedHomEquiv A E _ _ a) f.unop.toOrderHom).symm

variable (F G : DGFunctor A D E)
  (a : ∀ x : D, ForgetEnrichment.of (Complex A) (F.obj x) ⟶
    ForgetEnrichment.of (Complex A) (G.obj x))
  (h : ∀ x y : D, F.map x y ≫
    eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (F.obj x)) (a y) =
    G.map x y ≫ eHomWhiskerRight (Complex A) (a x)
      (ForgetEnrichment.of (Complex A) (G.obj y)))

include h

/-- 全 Hom 自然性は、元の閉定数との AW 合成の全高次単体上の自然性を与える。 -/
lemma dgStandardClosedComparison_naturality {x y : D} {n : ℕ}
    (s : StandardSimplex A x y n) :
    standardAW (standardConstant (closedHomEquiv A E _ _ (a y)) n)
        (dgStandardSimplexMap F s) =
      standardAW (dgStandardSimplexMap G s)
        (standardConstant (closedHomEquiv A E _ _ (a x)) n) := by
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (awData _ _).component J k hJ hk = (awData _ _).component J k hJ hk
  rw [awData_closed_post_component, awData_closed_pre_component]
  have he := congrArg (fun q => q.f k (s.val.component J k hJ hk)) (h x y)
  change (eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (F.obj x))
      (a y)).f k ((F.map x y).f k (s.val.component J k hJ hk)) =
    (eHomWhiskerRight (Complex A) (a x)
      (ForgetEnrichment.of (Complex A) (G.obj y))).f k
        ((G.map x y).f k (s.val.component J k hJ hk)) at he
  rw [dgClosedWhiskerLeft_f, dgClosedWhiskerRight_f] at he
  exact he

/-- 元の閉零比較は、標準 DK の全 Hom を保つ厳密な単体的豊穣自然変換。 -/
def dgStandardClosedComparison :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (dgStandardEnrichedFunctor F) (dgStandardEnrichedFunctor G) where
  app x := dgStandardClosedMap (a (ForgetEnrichment.to (Complex A) x))
  naturality x y := by
    ext n s
    change standardAW
        (standardConstant (closedHomEquiv A E _ _ (a (ForgetEnrichment.to (Complex A) y)))
          n.unop.len) (dgStandardSimplexMap F s.2) =
      standardAW (dgStandardSimplexMap G s.2)
        (standardConstant (closedHomEquiv A E _ _ (a (ForgetEnrichment.to (Complex A) x)))
          n.unop.len)
    exact dgStandardClosedComparison_naturality F G a h s.2

end SerrePositivity.KST.SConstruction
