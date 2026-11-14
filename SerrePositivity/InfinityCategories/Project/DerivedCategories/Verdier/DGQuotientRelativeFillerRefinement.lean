module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientRelativeFiller
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPrecompositionIdentity

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] {P : Set D} {m n : ℕ} {x : D} {y : Fin m → D}
variable {f : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x (y i) n}
variable {g : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A ((inclusion A D P).obj x) ((inclusion A D P).obj (y i)) n}

/-- 指定された一つの追加実分母で、全ての有限充填と実相対ホモトピーを細分する。 -/
def DGQuotientRelativeFiller.refineClosed (w : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientRelativeFiller A D P x y f g)
    {p : D} (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) w.source)
    (hr : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientRelativeFiller A D P x y f g where
  source := p
  denominator := r ≫ w.denominator
  denominator_mem := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_comp A D P r w.denominator hr w.denominator_mem
  simplex i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r) (w.simplex i)
  proper i J k hJ hk hne := by
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r).f k ((w.simplex i).val.component J k hJ hk) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_f, w.proper i J k hJ hk hne, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_comp]
  homotopy i := (w.homotopy i).refineClosed A D (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P)
    r w.denominator (g i) (w.simplex i)

/-- 追加細分の実ホモトピーは、保持していた実ホモトピーへの後合成。 -/
lemma DGQuotientRelativeFiller.refineClosed_h (w : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientRelativeFiller A D P x y f g)
    {p : D} (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) w.source)
    (hr : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) (i : Fin m) :
    ((w.refineClosed A D r hr).homotopy i).homotopy.h = (w.homotopy i).homotopy.h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A (QuotientObject D P)
        (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj p) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj w.source)
        (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i)) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map r)) :=
  (w.homotopy i).refineClosed_h A D (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P)
    r w.denominator (g i) (w.simplex i)

/-- 二回の追加細分は、実ホモトピーの台で指定合成分母の細分と厳密に一致。 -/
lemma DGQuotientRelativeFiller.refineClosed_comp_h (w : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientRelativeFiller A D P x y f g)
    {p q : D} (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) w.source)
    (l : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p)
    (hr : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (hl : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D l).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) (i : Fin m) :
    (((w.refineClosed A D r hr).refineClosed A D l hl).homotopy i).homotopy.h =
      ((w.refineClosed A D (l ≫ r)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_comp A D P l r hl hr)).homotopy i).homotopy.h := by
  let F := _root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P
  let R := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A (QuotientObject D P)
    (q := F.obj p) (x := F.obj w.source) (y := F.obj (y i)) (F.onClosed.map r))
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A (QuotientObject D P)
    (q := F.obj q) (x := F.obj p) (y := F.obj (y i)) (F.onClosed.map l))
  let LR := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A (QuotientObject D P)
    (q := F.obj q) (x := F.obj w.source) (y := F.obj (y i)) (F.onClosed.map (l ≫ r)))
  have hc : R ≫ L = LR := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp _ _).symm.trans
      (congrArg _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_map_comp A D (QuotientObject D P)
        F l r))
  have h1 := w.refineClosed_h A D r hr i
  have h2 := (w.refineClosed A D r hr).refineClosed_h A D l hl i
  have h3 := w.refineClosed_h A D (l ≫ r)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_comp A D P l r hl hr) i
  exact h2.trans ((congrArg (fun h => h ≫ L) h1).trans
    ((Category.assoc _ R L).trans ((congrArg (fun h => (w.homotopy i).homotopy.h ≫ h) hc).trans
      h3.symm)))

/-- 二回の細分は、元の充填単体についても合成分母の細分と厳密に一致。 -/
lemma DGQuotientRelativeFiller.refineClosed_comp_simplex
    (w : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientRelativeFiller A D P x y f g)
    {p q : D} (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) w.source)
    (l : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p)
    (hr : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (hl : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D l).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) (i : Fin m) :
    ((w.refineClosed A D r hr).refineClosed A D l hl).simplex i =
      (w.refineClosed A D (l ≫ r) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_comp A D P l r hl hr)).simplex i :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition_comp A D l r (w.simplex i)

/-- 恒等分母の細分は充填単体を変えない。 -/
lemma DGQuotientRelativeFiller.refineClosed_id_simplex
    (w : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientRelativeFiller A D P x y f g) (i : Fin m) :
    (w.refineClosed A D (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_id A D P w.source)).simplex i =
      w.simplex i := by
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D (𝟙 _)) (w.simplex i) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap_id]

/-- 恒等分母の細分は保持した実ホモトピーの台を変えない。 -/
lemma DGQuotientRelativeFiller.refineClosed_id_h
    (w : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientRelativeFiller A D P x y f g) (i : Fin m) :
    ((w.refineClosed A D (𝟙 _)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_id A D P w.source)).homotopy i).homotopy.h =
      (w.homotopy i).homotopy.h := by
  let F := _root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P
  have hi := F.onClosed.map_id (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) w.source)
  have hp := congrArg (fun e : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (F.obj w.source) ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (F.obj w.source) =>
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A (QuotientObject D P) (q := F.obj w.source)
      (x := F.obj w.source) (y := F.obj (y i)) e) hi
  have hc := (congrArg _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap
    (hp.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_id A (QuotientObject D P)))).trans _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_id
  exact (w.refineClosed_h A D (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_id A D P w.source) i).trans
    ((congrArg (fun h => (w.homotopy i).homotopy.h ≫ h) hc).trans (Category.comp_id _))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
