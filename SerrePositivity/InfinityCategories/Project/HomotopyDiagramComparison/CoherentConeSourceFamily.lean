module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeIdentitySection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceSourcePrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedStrictConeFamily

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
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {K : SSet.{max u v}} {p : K ⟶ SimplicialNerve C}

/-- 錐全体の標準 coslice 切断を、指定した頂点の対象で正規化する。 -/
def coherentConeSourceSectionAt (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (z : C)
    (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{max u v}) K ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneIdentityCosliceSection c ≫ eqToHom (congrArg
    (fun w : (SimplicialNerve C) _⦋0⦌ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w)) hz)

/-- 頂点を正規化しても標準切断は元の錐の図式を被覆する。 -/
lemma coherentConeSourceSectionAt_projection (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (z : C)
    (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) :
    coherentConeSourceSectionAt c z hz ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z)) = c.val := by
  have ht {a b : (SimplicialNerve C) _⦋0⦌} (h : a = b) :
      eqToHom (congrArg (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w)) h) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm a) := by
    cases h
    exact Category.id_comp _
  rw [coherentConeSourceSectionAt, Category.assoc, ht hz,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneIdentityCosliceSection_projection]

/-- 錐全体の標準切断の制限は、元の錐の coslice 表示の同じ正規化。 -/
lemma coherentConeSourceSectionAt_restrict (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (z : C)
    (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{max u v}) K ≫ coherentConeSourceSectionAt c z hz =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection c ≫ eqToHom (congrArg
        (fun w : (SimplicialNerve C) _⦋0⦌ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w)) hz) := by
  rw [coherentConeSourceSectionAt, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneIdentityCosliceSection_restrict]

/-- 錐の図式全体上の、指定した頂点への反転 Hom 全体の明示的な族。 -/
def coherentConeSourceFamily (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (z : C)
    (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace c.val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry
    ((coherentConeSourceSectionAt c z hz ▷
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coherentCosliceSourcePrecomposition x z) (by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coherentCosliceSourcePrecomposition_over, ← Category.assoc,
      whiskerRight_fst, Category.assoc, coherentConeSourceSectionAt_projection])

/-- 明示的な錐全体の族の評価は、標準切断に対する実際の coslice の前合成。 -/
lemma coherentConeSourceFamily_uncurry (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (z : C)
    (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (coherentConeSourceFamily c z hz x) =
      (coherentConeSourceSectionAt c z hz ▷
        (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coherentCosliceSourcePrecomposition x z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry _ _

/-- 明示的な錐全体の族を制限すると、元の錐の切断への同じ coslice の前合成になる。 -/
lemma coherentConeSourceFamily_restriction_uncurry (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (z : C)
    (hz : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex z) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
        (coherentConeSourceFamily c z hz x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x)) =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection c ≫ eqToHom (congrArg
        (fun w : (SimplicialNerve C) _⦋0⦌ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm w)) hz)) ▷
          (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x z).op) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coherentCosliceSourcePrecomposition x z := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.relativeFunctorUncurry_eqToHom _ c.property, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre,
    coherentConeSourceFamily_uncurry, ← comp_whiskerRight_assoc,
    coherentConeSourceSectionAt_restrict]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
