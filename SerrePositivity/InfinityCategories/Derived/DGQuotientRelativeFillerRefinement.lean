module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientRelativeFiller
public import SerrePositivity.InfinityCategories.Derived.DGClosedPrecompositionIdentity

/-! # 有限実相対充填の指定閉分母による反復細分

概要：保持した有限充填の全既知成分・分母条件・実相対ホモトピーを追加分母後でも保つ。
方針：元の単体は前合成し、実ホモトピーは像の前合成鎖写像で輸送する。
規約：二回の輸送の台は合成分母の輸送と厳密に一致。使われ方：屋根図式の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.PinchedHom
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D] {P : Set D} {m n : ℕ} {x : D} {y : Fin m → D}
variable {f : ∀ i, LinearData A x (y i) n}
variable {g : ∀ i, LinearSimplex A ((inclusion A D P).obj x) ((inclusion A D P).obj (y i)) n}

/-- 指定された一つの追加実分母で、全ての有限充填と実相対ホモトピーを細分する。 -/
def DGQuotientRelativeFiller.refineClosed (w : DGQuotientRelativeFiller A D P x y f g)
    {p : D} (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) w.source)
    (hr : (dgClosedEdge A D r).edge ∈ dgVerdierEdges A D P) :
    DGQuotientRelativeFiller A D P x y f g where
  source := p
  denominator := r ≫ w.denominator
  denominator_mem := dgClosedVerdierDenominator_comp A D P r w.denominator hr w.denominator_mem
  simplex i := pinchedLinearSimplexMap (dgClosedPrecomposition A D r) (w.simplex i)
  proper i J k hJ hk hne := by
    change (dgClosedPrecomposition A D r).f k ((w.simplex i).val.component J k hJ hk) = _
    rw [dgClosedPrecomposition_f, w.proper i J k hJ hk hne, dgGradedPrecompose_comp]
  homotopy i := (w.homotopy i).refineClosed A D (QuotientObject D P) (inclusion A D P)
    r w.denominator (g i) (w.simplex i)

/-- 追加細分の実ホモトピーは、保持していた実ホモトピーへの後合成。 -/
lemma DGQuotientRelativeFiller.refineClosed_h (w : DGQuotientRelativeFiller A D P x y f g)
    {p : D} (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) w.source)
    (hr : (dgClosedEdge A D r).edge ∈ dgVerdierEdges A D P) (i : Fin m) :
    ((w.refineClosed A D r hr).homotopy i).homotopy.h = (w.homotopy i).homotopy.h ≫
      pinchedHomChainMap (dgClosedPrecomposition A (QuotientObject D P)
        (q := (inclusion A D P).obj p) (x := (inclusion A D P).obj w.source)
        (y := (inclusion A D P).obj (y i)) ((inclusion A D P).onClosed.map r)) :=
  (w.homotopy i).refineClosed_h A D (QuotientObject D P) (inclusion A D P)
    r w.denominator (g i) (w.simplex i)

/-- 二回の追加細分は、実ホモトピーの台で指定合成分母の細分と厳密に一致。 -/
lemma DGQuotientRelativeFiller.refineClosed_comp_h (w : DGQuotientRelativeFiller A D P x y f g)
    {p q : D} (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) w.source)
    (l : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) p)
    (hr : (dgClosedEdge A D r).edge ∈ dgVerdierEdges A D P)
    (hl : (dgClosedEdge A D l).edge ∈ dgVerdierEdges A D P) (i : Fin m) :
    (((w.refineClosed A D r hr).refineClosed A D l hl).homotopy i).homotopy.h =
      ((w.refineClosed A D (l ≫ r)
        (dgClosedVerdierDenominator_comp A D P l r hl hr)).homotopy i).homotopy.h := by
  let F := inclusion A D P
  let R := pinchedHomChainMap (dgClosedPrecomposition A (QuotientObject D P)
    (q := F.obj p) (x := F.obj w.source) (y := F.obj (y i)) (F.onClosed.map r))
  let L := pinchedHomChainMap (dgClosedPrecomposition A (QuotientObject D P)
    (q := F.obj q) (x := F.obj p) (y := F.obj (y i)) (F.onClosed.map l))
  let LR := pinchedHomChainMap (dgClosedPrecomposition A (QuotientObject D P)
    (q := F.obj q) (x := F.obj w.source) (y := F.obj (y i)) (F.onClosed.map (l ≫ r)))
  have hc : R ≫ L = LR := by
    exact (pinchedHomChainMap_comp _ _).symm.trans
      (congrArg pinchedHomChainMap (dgClosedPrecomposition_map_comp A D (QuotientObject D P)
        F l r))
  have h1 := w.refineClosed_h A D r hr i
  have h2 := (w.refineClosed A D r hr).refineClosed_h A D l hl i
  have h3 := w.refineClosed_h A D (l ≫ r)
    (dgClosedVerdierDenominator_comp A D P l r hl hr) i
  exact h2.trans ((congrArg (fun h => h ≫ L) h1).trans
    ((Category.assoc _ R L).trans ((congrArg (fun h => (w.homotopy i).homotopy.h ≫ h) hc).trans
      h3.symm)))

/-- 二回の細分は、元の充填単体についても合成分母の細分と厳密に一致。 -/
lemma DGQuotientRelativeFiller.refineClosed_comp_simplex
    (w : DGQuotientRelativeFiller A D P x y f g)
    {p q : D} (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) w.source)
    (l : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) p)
    (hr : (dgClosedEdge A D r).edge ∈ dgVerdierEdges A D P)
    (hl : (dgClosedEdge A D l).edge ∈ dgVerdierEdges A D P) (i : Fin m) :
    ((w.refineClosed A D r hr).refineClosed A D l hl).simplex i =
      (w.refineClosed A D (l ≫ r) (dgClosedVerdierDenominator_comp A D P l r hl hr)).simplex i :=
  pinchedClosedPrecomposition_comp A D l r (w.simplex i)

/-- 恒等分母の細分は充填単体を変えない。 -/
lemma DGQuotientRelativeFiller.refineClosed_id_simplex
    (w : DGQuotientRelativeFiller A D P x y f g) (i : Fin m) :
    (w.refineClosed A D (𝟙 _) (dgClosedVerdierDenominator_id A D P w.source)).simplex i =
      w.simplex i := by
  change pinchedLinearSimplexMap (dgClosedPrecomposition A D (𝟙 _)) (w.simplex i) = _
  rw [dgClosedPrecomposition_id, pinchedLinearSimplexMap_id]

/-- 恒等分母の細分は保持した実ホモトピーの台を変えない。 -/
lemma DGQuotientRelativeFiller.refineClosed_id_h
    (w : DGQuotientRelativeFiller A D P x y f g) (i : Fin m) :
    ((w.refineClosed A D (𝟙 _)
      (dgClosedVerdierDenominator_id A D P w.source)).homotopy i).homotopy.h =
      (w.homotopy i).homotopy.h := by
  let F := inclusion A D P
  have hi := F.onClosed.map_id (ForgetEnrichment.of (Complex A) w.source)
  have hp := congrArg (fun e : ForgetEnrichment.of (Complex A) (F.obj w.source) ⟶
      ForgetEnrichment.of (Complex A) (F.obj w.source) =>
    dgClosedPrecomposition A (QuotientObject D P) (q := F.obj w.source)
      (x := F.obj w.source) (y := F.obj (y i)) e) hi
  have hc := (congrArg pinchedHomChainMap
    (hp.trans (dgClosedPrecomposition_id A (QuotientObject D P)))).trans pinchedHomChainMap_id
  exact (w.refineClosed_h A D (𝟙 _) (dgClosedVerdierDenominator_id A D P w.source) i).trans
    ((congrArg (fun h => (w.homotopy i).homotopy.h ≫ h) hc).trans (Category.comp_id _))

end SerrePositivity.InfinityCategories
