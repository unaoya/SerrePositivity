module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeIdentitySection
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceSourcePrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedStrictConeFamily

/-!
概要：任意の coherent な錐の図式全体上に、実際の豊穣 Hom の族を構成する。
方針：錐全体の標準 coslice 切断に、coslice 全体の全パラメータの前合成を作用させる。
規約：頂点評価の逆の選択を用いない。標準 Hom 比較との頂点での同定は別途検証する。
使われ方：HTT 4.2.4.1 の coend 余錐の普遍性を与える錐全体の比較族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {K : SSet.{max u v}} {p : K ⟶ SimplicialNerve C}

/-- 錐全体の標準 coslice 切断を、指定した頂点の対象で正規化する。 -/
def coherentConeSourceSectionAt (c : JoinCone p) (z : C)
    (hz : c.vertex = coherentNerveVertex z) :
    join (Δ[0] : SSet.{max u v}) K ⟶
      sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex z)) :=
  coneIdentityCosliceSection c ≫ eqToHom (congrArg
    (fun w : (SimplicialNerve C) _⦋0⦌ ↦ sliceUnder (SSet.yonedaEquiv.symm w)) hz)

/-- 頂点を正規化しても標準切断は元の錐の図式を被覆する。 -/
lemma coherentConeSourceSectionAt_projection (c : JoinCone p) (z : C)
    (hz : c.vertex = coherentNerveVertex z) :
    coherentConeSourceSectionAt c z hz ≫
        sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex z)) = c.val := by
  have ht {a b : (SimplicialNerve C) _⦋0⦌} (h : a = b) :
      eqToHom (congrArg (fun w ↦ sliceUnder (SSet.yonedaEquiv.symm w)) h) ≫
        sliceUnderProjection (SSet.yonedaEquiv.symm b) =
          sliceUnderProjection (SSet.yonedaEquiv.symm a) := by
    cases h
    exact Category.id_comp _
  rw [coherentConeSourceSectionAt, Category.assoc, ht hz,
    coneIdentityCosliceSection_projection]

/-- 錐全体の標準切断の制限は、元の錐の coslice 表示の同じ正規化。 -/
lemma coherentConeSourceSectionAt_restrict (c : JoinCone p) (z : C)
    (hz : c.vertex = coherentNerveVertex z) :
    joinInr (Δ[0] : SSet.{max u v}) K ≫ coherentConeSourceSectionAt c z hz =
      coherentConeCosliceSection c ≫ eqToHom (congrArg
        (fun w : (SimplicialNerve C) _⦋0⦌ ↦ sliceUnder (SSet.yonedaEquiv.symm w)) hz) := by
  rw [coherentConeSourceSectionAt, ← Category.assoc, coneIdentityCosliceSection_restrict]

/-- 錐の図式全体上の、指定した頂点への反転 Hom 全体の明示的な族。 -/
def coherentConeSourceFamily (c : JoinCone p) (z : C)
    (hz : c.vertex = coherentNerveVertex z) (x : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op ⟶
      coherentConeSectionSpace c.val (coherentNerveVertex x) :=
  relativeFunctorCurry
    ((coherentConeSourceSectionAt c z hz ▷
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op) ≫
        coherentCosliceSourcePrecomposition x z) (by
    rw [Category.assoc, coherentCosliceSourcePrecomposition_over, ← Category.assoc,
      whiskerRight_fst, Category.assoc, coherentConeSourceSectionAt_projection])

/-- 明示的な錐全体の族の評価は、標準切断に対する実際の coslice の前合成。 -/
lemma coherentConeSourceFamily_uncurry (c : JoinCone p) (z : C)
    (hz : c.vertex = coherentNerveVertex z) (x : C) :
    relativeFunctorUncurry (coherentConeSourceFamily c z hz x) =
      (coherentConeSourceSectionAt c z hz ▷
        (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op) ≫
          coherentCosliceSourcePrecomposition x z :=
  relativeFunctorUncurry_curry _ _

/-- 明示的な錐全体の族を制限すると、元の錐の切断への同じ coslice の前合成になる。 -/
lemma coherentConeSourceFamily_restriction_uncurry (c : JoinCone p) (z : C)
    (hz : c.vertex = coherentNerveVertex z) (x : C) :
    relativeFunctorUncurry
        (coherentConeSourceFamily c z hz x ≫ coneSectionRestriction c (coherentNerveVertex x)) =
      ((coherentConeCosliceSection c ≫ eqToHom (congrArg
        (fun w : (SimplicialNerve C) _⦋0⦌ ↦ sliceUnder (SSet.yonedaEquiv.symm w)) hz)) ▷
          (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op) ≫
            coherentCosliceSourcePrecomposition x z := by
  rw [coneSectionRestriction, ← Category.assoc,
    relativeFunctorUncurry_eqToHom _ c.property, relativeFunctorUncurry_pre,
    coherentConeSourceFamily_uncurry, ← comp_whiskerRight_assoc,
    coherentConeSourceSectionAt_restrict]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
