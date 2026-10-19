module
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Derived.PinchedLinearFunctorLaws

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]
variable [Small.{u} D] [Small.{u} E] (F : DGFunctor A D E)

/-- 閉射の前合成鎖写像は dg 関手の Hom 鎖写像と厳密に可換。 -/
lemma dgClosedPrecomposition_naturality {p q y : D}
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    dgClosedPrecomposition A D (y := y) r ≫ F.map p y =
      F.map q y ≫ dgClosedPrecomposition A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
        (F.onClosed.map r) := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (F.map p y).f k ((dgClosedPrecomposition A D r).f k a) =
    (dgClosedPrecomposition A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
      (F.onClosed.map r)).f k ((F.map q y).f k a)
  rw [dgClosedPrecomposition_f, dgClosedPrecomposition_f, dgFunctorGradedPrecompose_map]

/-- 元の線形単体を前合成してから写すことと、像を前合成することは一致。 -/
lemma pinchedClosedPrecomposition_naturality {p q y : D}
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    {n : ℕ} (s : LinearSimplex A q y n) :
    pinchedLinearSimplexMap (F.map p y)
      (pinchedLinearSimplexMap (dgClosedPrecomposition A D r) s) =
      pinchedLinearSimplexMap
        (dgClosedPrecomposition A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
          (F.onClosed.map r)) (pinchedLinearSimplexMap (F.map q y) s) := by
  rw [pinchedLinearSimplexMap_comp, pinchedLinearSimplexMap_comp,
    dgClosedPrecomposition_naturality]

/-- 閉分母二本による線形前合成は、指定した合成分母の前合成と一致。 -/
lemma pinchedClosedPrecomposition_comp {p q x y : D}
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
    {n : ℕ} (g : LinearSimplex A x y n) :
    pinchedLinearSimplexMap (dgClosedPrecomposition A D r)
      (pinchedLinearSimplexMap (dgClosedPrecomposition A D s) g) =
      pinchedLinearSimplexMap (dgClosedPrecomposition A D (r ≫ s)) g := by
  rw [pinchedLinearSimplexMap_comp, dgClosedPrecomposition_comp]

omit [Small.{u} D] in
/-- 二本の閉射の像による前合成鎖写像の合成は、元の合成射の像による前合成。 -/
lemma dgClosedPrecomposition_map_comp {p q x y : D}
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    dgClosedPrecomposition A E (q := F.obj q) (x := F.obj x) (y := F.obj y)
      (F.onClosed.map s) ≫
    dgClosedPrecomposition A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
      (F.onClosed.map r) =
    dgClosedPrecomposition A E (q := F.obj p) (x := F.obj x) (y := F.obj y)
      (F.onClosed.map (r ≫ s)) :=
  (dgClosedPrecomposition_comp A E (p := F.obj p) (q := F.obj q) (x := F.obj x)
    (y := F.obj y) (F.onClosed.map r) (F.onClosed.map s)).trans
      (congrArg (fun e : ForgetEnrichment.of (Complex A) (F.obj p) ⟶
          ForgetEnrichment.of (Complex A) (F.obj x) =>
        dgClosedPrecomposition A E (q := F.obj p) (x := F.obj x) (y := F.obj y) e)
          (F.onClosed.map_comp r s).symm)

end SerrePositivity.InfinityCategories
