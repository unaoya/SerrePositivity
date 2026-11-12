module

public import SerrePositivity.KST.NonConnective.DGKappaZeroPerfAction
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGNativeActionFixed

/-!
概要：同じ dg cone の全 native 関手族による、元の実 Perf 上の全作用。
方針：既存の実 tensor 作用を curry し、元の厳密関手での固定を全単体で回収する。
規約：非可逆な注入・射影も受け取る全族を使用する。
使われ方：同じ実分裂 cofiber 図式を Perf の関手空間へ送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
private lemma fullPerfFamilyVertex {A B P : SSet.{w}}
    (F : P ⟶ (ihom A).obj B) (p : P _⦋0⦌) (f : A ⟶ B)
    (h : (SSet.unitHomEquiv P).symm p ≫ F = curry' f) :
    F.app (Opposite.op ⦋0⦌) p = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f := by
  have h := congrArg (SSet.unitHomEquiv _) h
  change F.app (Opposite.op ⦋0⦌)
    ((SSet.unitHomEquiv P) ((SSet.unitHomEquiv P).symm p)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f at h
  simpa only [Equiv.apply_symm_apply] using h

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ cone の全 native dg 関手圏を、元の Perf の出力宇宙へ移す。 -/
abbrev dgKappaFullPerfParameter : SSet.{max (u + 1) v} :=
  (SSet.uliftFunctor.{u + 1, max (u + 1) v}).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)))

/-- 同じ全 native 関手族による、元の Perf の全関手空間への実作用。 -/
def dgKappaFullPerfFamilyMap : dgKappaFullPerfParameter R D I ⟶
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I)))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I))) :=
  curry (presentedPerfectDGNativeAction R (DGKappaCone R D I) (DGKappaCone R D I))

/-- 元の同じ厳密 dg 関手を全 native 関手族の実単位射として保持する。 -/
def dgKappaFullPerfParameterPoint (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)) :
    𝟙_ SSet.{max (u + 1) v} ⟶ dgKappaFullPerfParameter R D I :=
  (SSet.unitHomEquiv _).symm (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex F))

/-- 同じ実単位射は全次数で元の閉単位からの native 定数単体。 -/
lemma dgKappaFullPerfParameterPoint_app
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I))
    (n : SimplexCategoryᵒᵖ) (a : (𝟙_ SSet.{max (u + 1) v}).obj n) :
    ((dgKappaFullPerfParameterPoint R D I F).app n a).down =
      dgNativePointSimplex R (_root_.SerrePositivity.DifferentialGraded.DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I))
        F n.unop.len := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex F).pullback
    (SimplexCategory.const n.unop ⦋0⦌ 0).toOrderHom = _
  rw [← dgNativePointSimplex_zero]
  exact dgNativePointSimplex_pullback R _ F _

/-- 全実作用を元の同じ厳密関手に固定すると、元の Perf の全単体作用に戻る。 -/
lemma dgKappaFullPerfFamilyMap_fixed
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)) :
    dgKappaFullPerfParameterPoint R D I F ≫ dgKappaFullPerfFamilyMap R D I =
      curry' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I) F)) := by
  rw [dgKappaFullPerfFamilyMap, ← curry_natural_left, curry', ← id_tensorHom]
  congr 1
  ext n p
  rcases p with ⟨x, a⟩
  change presentedPerfectDGNativeActionSimplex R (DGKappaCone R D I) (DGKappaCone R D I)
      x (((dgKappaFullPerfParameterPoint R D I F).app n a).down) =
    x.map (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I) F)
  rw [dgKappaFullPerfParameterPoint_app]
  exact presentedPerfectDGNativeActionSimplex_fixed R _ _ x F

/-- 同じ全作用の指定入力頂点は、元の Perf 厳密作用の関手頂点そのもの。 -/
lemma dgKappaFullPerfFamilyMap_vertex
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)) :
    (dgKappaFullPerfFamilyMap R D I).app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex F)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I) F)) := by
  exact fullPerfFamilyVertex (dgKappaFullPerfFamilyMap R D I)
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex F)) _ (dgKappaFullPerfFamilyMap_fixed R D I F)

end SerrePositivity.KST.NonConnective
