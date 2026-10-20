module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingPinchedFamilyEvaluation
public import SerrePositivity.InfinityCategories.Derived.PinchedFamilyPostcomposition
public import SerrePositivity.InfinityCategories.Derived.PinchedSliceCompositionRealization
/-!
概要：任意標的への dg 屋根の評価方程式を、同じ分母の全区間を持つ実 slice 比較へ戻す。
方針：定値端点の共役を解き、実 pinched Hom 族の合成方程式を実現する。
規約：パラメータの有限性を仮定しない。使われ方：反転屋根内の族比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable {K : SSet.{max u v}} {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y)
variable {q x y : D}
variable (d : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
variable (n : K ⟶ DGNerve.pinchedHom A D q y)
variable (e : DGInvertingPinchedFamilyEvaluation A D F d n)
/-- 実評価族は、像の分母と像の分子に対する同じ関手圏内の方程式を満たす。 -/
lemma dgInvertingPinchedFamilyEvaluation_equation :
    intervalFamilyHom ((SSet.const (X := K) (pinchedClosedVertex A D d) ≫
      pinchedHomMap F (Simplex.vertex q) (Simplex.vertex x)) ≫
        pinchedHomToIntervalMappingSpace _ _) ≫
      intervalFamilyHom (e.value ≫ pinchedHomToIntervalMappingSpace _ _) =
        intervalFamilyHom ((n ≫ pinchedHomMap F (Simplex.vertex q) (Simplex.vertex y)) ≫
          pinchedHomToIntervalMappingSpace _ _) := by
  let i := constantFunctorCompIso K (Simplex.vertex q) F
  let j := constantFunctorCompIso K (Simplex.vertex x) F
  let k := constantFunctorCompIso K (Simplex.vertex y) F
  let G := (hoFunctor.map ((ihom K).map F)).toFunctor
  have hd := pinchedFamilyHom_postcomp F (SSet.const (X := K) (pinchedClosedVertex A D d))
  have hn := pinchedFamilyHom_postcomp F n
  calc
    _ = (i.inv ≫ G.map (dgPinchedFamilyHom A D
        (SSet.const (X := K) (pinchedClosedVertex A D d))) ≫ j.hom) ≫
          (j.inv ≫ e.evaluation.value ≫ k.hom) :=
      congrArg₂ (fun a b => a ≫ b) hd e.value_eq
    _ = i.inv ≫ G.map (dgPinchedFamilyHom A D n) ≫ k.hom :=
      roofConjugatedEvaluation_fac i j k _ _ _ e.evaluation.fac
    _ = _ := hn.symm
/-- 実分母の像を全時刻の底に持つ、指定評価族の実 slice 比較。 -/
abbrev DGInvertingPinchedSliceRealization :=
  PinchedSliceCompositionRealization
    (SSet.const (X := K) (pinchedClosedVertex A D d) ≫
      pinchedHomMap F (Simplex.vertex q) (Simplex.vertex x)) e.value
    (n ≫ pinchedHomMap F (Simplex.vertex q) (Simplex.vertex y))
/-- 任意の実評価族に、始点補正三角形も保持する実 slice 比較が存在する。 -/
lemma dgInvertingPinchedSliceRealization_nonempty [Quasicategory Y] :
    Nonempty (DGInvertingPinchedSliceRealization A D F d n e) :=
  pinchedSliceCompositionRealization_nonempty _ _ _
    (dgInvertingPinchedFamilyEvaluation_equation A D F d n e)
end SerrePositivity.InfinityCategories
