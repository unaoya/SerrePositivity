module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveOppositeIso
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor
/-!
概要：実反対圏比較と、任意の dg 関手の全単体作用との厳密な自然性。
方針：全 Hom の鎖写像が反転符号と可換なことを全成分へ適用する。
規約：対象別の同型ではなく実 ∞ 関手の等式。使われ方：反変 Hom の模型変更。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
/-- 符号付き実反転は、dg 関手の全実成分への作用と厳密に可換。 -/
lemma dgOppositeData_map {R : Type u} [CommRing R] {D : Type v} {E : Type w}
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op (s.map F) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op s).map F.op := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map, DGFunctor.op, id_eq,
      Units.smul_def, map_zsmul]
    rfl
/-- 同じ実 dg 関手の nerve に関して、反対圏比較の全四角形は厳密に可換。 -/
lemma dgNerveOppositeIso_naturality {R : Type u} [CommRing R] {D E : Type v}
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R E).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R D).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F.op := by
  ext n s
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex ((SSet.opObjEquiv s).map F) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex (SSet.opObjEquiv s)).map F.op
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOppositeData_map (SSet.opObjEquiv s).toSimplexData F
end SerrePositivity.InfinityCategories.Project.DerivedCategories
