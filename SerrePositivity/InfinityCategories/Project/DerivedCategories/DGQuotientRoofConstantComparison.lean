module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientRoofRefinementEquivalence

/-! # 固定商写像空間から商側の屋根図式への自然比較

概要：商内の Hom(x,y) の定値図式から、分母前合成で各屋根 Hom へ自然に写す。
方針：閉前合成の合成則と厳密 Over の三角等式を使い、商での分母反転で各値の同値性を得る。
規約：逆写像や逆射の選択は使わない。使われ方：元の屋根図式との自然比較の span。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open scoped _root_.Simplicial
open CategoryTheory Opposite DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 元の厳密分母添字上で、商内の元の固定写像空間を値とする定値図式。 -/
def dgQuotientRoofConstant (P : Set D) (x y : D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)ᵒᵖ ⥤ SSet.{max u v} :=
  (Functor.const _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
    ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))

/-- 商内の固定写像空間から各屋根の写像空間への、元の分母の像による自然な前合成。 -/
def dgQuotientRoofConstantComparison (P : Set D) (x y : D) :
    dgQuotientRoofConstant A D P x y ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofDiagram A D P x y where
  app s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
    (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.unop.obj.left))
    (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)
    ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map s.unop.obj.hom)
  naturality {s t} r := by
    change 𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap _
    rw [Category.id_comp, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_comp]
    change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A (QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map t.unop.obj.hom)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A (QuotientObject D P)
        ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map r.unop.hom.left ≫
          (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map s.unop.obj.hom))
    rw [← Functor.map_comp, Over.w r.unop.hom]

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 指定実細分後の定値比較は、既存屋根での比較と図式の細分写像の合成。 -/
lemma dgQuotientRoofConstantComparison_refine (P : Set D) (x y : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) {q : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ s.obj.left)
    (hr : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) {n : ℕ}
    (g : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) _⦋n⦌) :
    SSet.yonedaEquiv.symm
      (((dgQuotientRoofConstantComparison A D P x y).app (op s)).app (op ⦋n⦌) g) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofDiagram A D P x y).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefineHom A D P x s r hr).op =
    SSet.yonedaEquiv.symm g ≫ (dgQuotientRoofConstantComparison A D P x y).app
      (op (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefine A D P x s r hr)) := by
  have hn := (dgQuotientRoofConstantComparison A D P x y).naturality
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefineHom A D P x s r hr).op
  change 𝟙 _ ≫ _ = _ at hn
  rw [Category.id_comp] at hn
  have hg : SSet.yonedaEquiv.symm
      (((dgQuotientRoofConstantComparison A D P x y).app (op s)).app (op ⦋n⦌) g) =
      SSet.yonedaEquiv.symm g ≫ (dgQuotientRoofConstantComparison A D P x y).app (op s) := by
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  rw [hg, Category.assoc, ← hn]

/-- 固定商 Hom から各実屋根への比較は、各添字で実ホモトピー同値。 -/
lemma dgQuotientRoofConstantComparison_app_equivalence (P : Set D)
    (hP : localKFlat A D P) (x y : D) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      ((dgQuotientRoofConstantComparison A D P x y).app (op s)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition_equivalence_of_invertible A (QuotientObject D P) _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedDenominator_isInvertible A D P hP s.obj.hom s.property)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
