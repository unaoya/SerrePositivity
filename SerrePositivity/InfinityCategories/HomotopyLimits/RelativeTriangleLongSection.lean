module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeTriangleFamilies

/-!
概要：任意の実際の三角形の長辺の全余錐族を、底を保つ三角形全体の族へ延長する。
方針：底の長辺制限の切断を選び、上の長辺と底の三角形族を相対制限へ一緒に持ち上げる。
規約：底の三角形の退化は仮定しない。長辺の全パラメータと可変終点を厳密に保つ。
使われ方：非退化な native 輸送三角形を通した、全 Hom の三面の整合する族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 任意の三角形の長辺の余錐空間を、同じ三角形全体へ延長する切断。 -/
def triangleLongCosliceSection {B : SSet.{u}} [Quasicategory B]
    (t : (Δ[2] : SSet.{u}) ⟶ B) :
    sliceUnder (stdSimplex.δ (1 : Fin 3) ≫ t) ⟶ sliceUnder t := by
  have := sliceUnderRestrict_triangleLongEdge t
  exact (trivialKanFibration_exists_section
    (sliceUnderRestrict t (stdSimplex.δ (1 : Fin 3)))).choose

/-- 長辺からの延長は、元の長辺の全余錐族を厳密に回収する。 -/
lemma triangleLongCosliceSection_long {B : SSet.{u}} [Quasicategory B]
    (t : (Δ[2] : SSet.{u}) ⟶ B) :
    triangleLongCosliceSection t ≫ sliceUnderRestrict t (stdSimplex.δ (1 : Fin 3)) = 𝟙 _ := by
  have := sliceUnderRestrict_triangleLongEdge t
  exact (trivialKanFibration_exists_section
    (sliceUnderRestrict t (stdSimplex.δ (1 : Fin 3)))).choose_spec

/-- 上の長辺と底の三角形族の両方を厳密に指定した、任意の三角形の相対延長。 -/
lemma exists_relativeTriangleLongFamily {E B T : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (a : T ⟶ sliceUnder (stdSimplex.δ (1 : Fin 3) ≫ t))
    (b : T ⟶ sliceUnder (t ≫ q))
    (h : a ≫ sliceUnderPostcomp (stdSimplex.δ (1 : Fin 3) ≫ t) q =
      b ≫ sliceUnderRestrict (t ≫ q) (stdSimplex.δ (1 : Fin 3))) :
    ∃ l : T ⟶ sliceUnder t,
      l ≫ sliceUnderRestrict t (stdSimplex.δ (1 : Fin 3)) = a ∧
        l ≫ sliceUnderPostcomp t q = b := by
  have := relativeCosliceRestriction_triangleLongEdge t q
  let v := pullback.lift a b h
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section
    (relativeCosliceRestriction t q (stdSimplex.δ (1 : Fin 3)))
  refine ⟨v ≫ s, ?_, ?_⟩
  · have ht := congrArg (fun z ↦ v ≫ z ≫ pullback.fst _ _) hs
    simpa only [relativeCosliceRestriction, squareComparison, Category.assoc,
      pullback.lift_fst, Category.id_comp, v] using ht
  · have ht := congrArg (fun z ↦ v ≫ z ≫ pullback.snd _ _) hs
    simpa only [relativeCosliceRestriction, squareComparison, Category.assoc,
      pullback.lift_snd, Category.id_comp, v] using ht

/-- 底で選んだ同じ三角形延長を保つ、上の長辺の全余錐空間の相対切断。 -/
def relativeTriangleLongSection {E B : SSet.{u}} [Quasicategory B]
    (t : (Δ[2] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q] :
    sliceUnder (stdSimplex.δ (1 : Fin 3) ≫ t) ⟶ sliceUnder t :=
  (exists_relativeTriangleLongFamily t q (𝟙 _)
    (sliceUnderPostcomp (stdSimplex.δ (1 : Fin 3) ≫ t) q ≫ triangleLongCosliceSection (t ≫ q))
    (by
      simp only [Category.assoc, triangleLongCosliceSection_long, Category.id_comp]
      exact (Category.comp_id _).symm)).choose

/-- 選んだ同じ相対切断は、長辺の全族を厳密に保つ。 -/
lemma relativeTriangleLongSection_long {E B : SSet.{u}} [Quasicategory B]
    (t : (Δ[2] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q] :
    relativeTriangleLongSection t q ≫ sliceUnderRestrict t (stdSimplex.δ (1 : Fin 3)) = 𝟙 _ :=
  (exists_relativeTriangleLongFamily t q (𝟙 _)
    (sliceUnderPostcomp (stdSimplex.δ (1 : Fin 3) ≫ t) q ≫ triangleLongCosliceSection (t ≫ q))
    (by
      simp only [Category.assoc, triangleLongCosliceSection_long, Category.id_comp]
      exact (Category.comp_id _).symm)).choose_spec.1

/-- 底の三角形族も、同じ切断で長辺から延長した族そのもの。 -/
lemma relativeTriangleLongSection_base {E B : SSet.{u}} [Quasicategory B]
    (t : (Δ[2] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q] :
    relativeTriangleLongSection t q ≫ sliceUnderPostcomp t q =
      sliceUnderPostcomp (stdSimplex.δ (1 : Fin 3) ≫ t) q ≫ triangleLongCosliceSection (t ≫ q) :=
  (exists_relativeTriangleLongFamily t q (𝟙 _)
    (sliceUnderPostcomp (stdSimplex.δ (1 : Fin 3) ≫ t) q ≫ triangleLongCosliceSection (t ≫ q))
    (by
      simp only [Category.assoc, triangleLongCosliceSection_long, Category.id_comp]
      exact (Category.comp_id _).symm)).choose_spec.2

/-- 三角形全体へ延長しても、可変な余錐の終点は全単体で厳密に保つ。 -/
lemma relativeTriangleLongSection_projection {E B : SSet.{u}} [Quasicategory B]
    (t : (Δ[2] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q] :
    relativeTriangleLongSection t q ≫ sliceUnderProjection t =
      sliceUnderProjection (stdSimplex.δ (1 : Fin 3) ≫ t) := by
  rw [← sliceUnderRestrict_projection t (stdSimplex.δ (1 : Fin 3)), ← Category.assoc,
    relativeTriangleLongSection_long, Category.id_comp]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
