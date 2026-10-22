module
public import SerrePositivity.KST.SConstruction.DGPerfectEndIsoComparison
public import SerrePositivity.KST.SConstruction.DGEndIsoIntertwining
public import SerrePositivity.KST.SConstruction.DGClosedComparisonIso

/-! # 同じ perfect End 比較の実代表加群上の作用
概要：元の perfect 加群の End 作用と、比較先の代表加群上の作用を同じ閉同型で結ぶ。
方針：同じ Yoneda 逆律で共役を回収し、元の閉同型の全 Hom 可換式を使う。
規約：全次数自然性と元の成分を保持。使われ方：商 End の cone 作用との実比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (M : PerfectDGModule R E) (b : E)
  (e : ForgetEnrichment.of (Complex R) M.val ≅
    ForgetEnrichment.of (Complex R) (representable R b))

/-- 同じ対象 End 比較を元の Yoneda で戻すと、同じ閉共役を厳密に回収する。 -/
lemma dgPerfectEndIsoObjectHom_yoneda :
    dgPerfectEndIsoObjectHom R E M b e ≫ yonedaHom R E b b =
      dgPerfectEndIsoModuleHom R E M b e := by
  change (dgEndIsoHom R (D := RightModule R E) e ≫
    (dgYonedaIso R b (representable R b)).hom) ≫
      (dgYonedaIso R b (representable R b)).inv = dgEndIsoHom R e
  erw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 元の perfect End が元の実加群上に作用する同じ dg 関手。 -/
def dgPerfectEndRepresentationSource : DGFunctor R (EndomorphismObject M) (RightModule R E) :=
  (endomorphismInclusion R M).comp (perfectDGModuleInclusion R E Set.univ)

/-- 元の対象 End 比較を同じ実 Yoneda へ送る dg 関手。 -/
def dgPerfectEndRepresentationTarget : DGFunctor R (EndomorphismObject M) (RightModule R E) :=
  ((dgPerfectEndIsoObjectFunctor R E M b e).comp (endomorphismInclusion R b)).comp (dgYoneda R E)

/-- 同じ元の実加群上の全 End 作用は恒等の Hom 写像。 -/
lemma dgPerfectEndRepresentationSource_map (x y : EndomorphismObject M) :
    (dgPerfectEndRepresentationSource R E M).map x y = 𝟙 _ := by
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  exact Category.comp_id _

/-- 比較先の同じ実代表加群上の全 Hom 作用は、同じ閉共役そのもの。 -/
lemma dgPerfectEndRepresentationTarget_map (x y : EndomorphismObject M) :
    (dgPerfectEndRepresentationTarget R E M b e).map x y =
      dgPerfectEndIsoModuleHom R E M b e := by
  change ((dgPerfectEndIsoObjectFunctor R E M b e).map x y ≫ 𝟙 _) ≫ yonedaHom R E b b = _
  rw [Category.comp_id, dgPerfectEndIsoObjectFunctor_map]
  exact dgPerfectEndIsoObjectHom_yoneda R E M b e

/-- 元の閉同型は、二つの実 End 表現を全 Hom 複体に関して結ぶ。 -/
lemma dgPerfectEndRepresentation_naturality (x y : EndomorphismObject M) :
    (dgPerfectEndRepresentationSource R E M).map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) M.val) e.hom =
    (dgPerfectEndRepresentationTarget R E M b e).map x y ≫
      eHomWhiskerRight (Complex R) e.hom
        (ForgetEnrichment.of (Complex R) (representable R b)) := by
  rw [dgPerfectEndRepresentationSource_map, dgPerfectEndRepresentationTarget_map]
  erw [Category.id_comp]
  exact (dgEndIsoHom_intertwining R (D := RightModule R E) e).symm

/-- 任意の元の Hom 写像を前合成しても、同じ全次数可換式を保持する。 -/
lemma dgPerfectEndRepresentation_precompose {K : Complex R}
    (f : K ⟶ homObject R (PerfectDGModule R E) M M) :
    f ≫ eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) M.val) e.hom =
      (f ≫ dgPerfectEndIsoModuleHom R E M b e) ≫
        eHomWhiskerRight (Complex R) e.hom
          (ForgetEnrichment.of (Complex R) (representable R b)) := by
  exact (congrArg (fun h => f ≫ h)
    (dgEndIsoHom_intertwining R (D := RightModule R E) e).symm).trans
      (Category.assoc _ _ _).symm

/-- 同じ元の閉同型を成分に持つ、全次数自然な実 End 表現比較。 -/
def dgPerfectEndRepresentationComparison :=
  dgFunctorClosedComparison R (dgPerfectEndRepresentationSource R E M)
    (dgPerfectEndRepresentationTarget R E M b e) (fun _ => e.hom)
    (dgPerfectEndRepresentation_naturality R E M b e)

/-- 同じ元の閉同型の逆を成分に持つ、全次数自然な逆比較。 -/
def dgPerfectEndRepresentationInverseComparison :=
  dgFunctorClosedInverseComparison R (dgPerfectEndRepresentationSource R E M)
    (dgPerfectEndRepresentationTarget R E M b e) (fun _ => e)
    (dgPerfectEndRepresentation_naturality R E M b e)

/-- 全 Hom 自然性を保つ同じ成分から得る、元の閉零表現の自然同型。 -/
def dgPerfectEndRepresentationClosedIso :
    (dgPerfectEndRepresentationSource R E M).onClosed ≅
      (dgPerfectEndRepresentationTarget R E M b e).onClosed :=
  dgFunctorClosedComparisonIso R _ _ (fun _ => e)
    (dgPerfectEndRepresentation_naturality R E M b e)

end SerrePositivity.KST.SConstruction
