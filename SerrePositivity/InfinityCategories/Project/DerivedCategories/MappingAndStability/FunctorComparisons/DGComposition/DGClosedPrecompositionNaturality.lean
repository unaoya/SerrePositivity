module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedLinearFunctorLaws

/-! # 閉分母の前合成鎖写像の dg 関手自然性

概要：元の閉射による前合成は、全 Hom の dg 関手の鎖写像と厳密に可換する。
方針：全整数次数で斉次前合成の既存の自然性へ帰着する。
規約：対象を明示して閉零圏の強制変換を固定する。使われ方：追加分母後の端点の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
variable [Small.{u} D] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- 閉射の前合成鎖写像は dg 関手の Hom 鎖写像と厳密に可換。 -/
lemma dgClosedPrecomposition_naturality {p q y : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D (y := y) r ≫ F.map p y =
      F.map q y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
        (F.onClosed.map r) := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (F.map p y).f k ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r).f k a) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
      (F.onClosed.map r)).f k ((F.map q y).f k a)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorGradedPrecompose_map]

/-- 元の線形単体を前合成してから写すことと、像を前合成することは一致。 -/
lemma pinchedClosedPrecomposition_naturality {p q y : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A q y n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (F.map p y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r) s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
          (F.onClosed.map r)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (F.map q y) s) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap_comp,
    dgClosedPrecomposition_naturality]

/-- 閉分母二本による線形前合成は、指定した合成分母の前合成と一致。 -/
lemma pinchedClosedPrecomposition_comp {p q x y : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D s) g) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D (r ≫ s)) g := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_comp]

omit [Small.{u} D] in
/-- 二本の閉射の像による前合成鎖写像の合成は、元の合成射の像による前合成。 -/
lemma dgClosedPrecomposition_map_comp {p q x y : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E (q := F.obj q) (x := F.obj x) (y := F.obj y)
      (F.onClosed.map s) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
      (F.onClosed.map r) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E (q := F.obj p) (x := F.obj x) (y := F.obj y)
      (F.onClosed.map (r ≫ s)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_comp A E (p := F.obj p) (q := F.obj q) (x := F.obj x)
    (y := F.obj y) (F.onClosed.map r) (F.onClosed.map s)).trans
      (congrArg (fun e : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (F.obj p) ⟶
          ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (F.obj x) =>
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E (q := F.obj p) (x := F.obj x) (y := F.obj y) e)
          (F.onClosed.map_comp r s).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
