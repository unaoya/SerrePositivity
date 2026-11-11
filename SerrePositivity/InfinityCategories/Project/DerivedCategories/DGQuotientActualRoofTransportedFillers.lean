module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofTransportedFiller
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientActualRoofRelativeFillers

/-! # 有限族の実屋根充填を元の商目標へ同時に輸送する

概要：一つの共通閉細分の上で、有限族の充填に全境界付き相対輸送三角形を供給する。
方針：既存の有限同時充填の各境界固定比較を、商屋根の左ファイブレーションで輸送する。
規約：全ての族に同じ指定細分辺を使う。使われ方：β3 の有限相対比較の主入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 有限族は一つの共通細分で充填され、元の商目標への全境界付き輸送を持つ。 -/
theorem dgQuotientRoofFinite_exists_transportedFillerData (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
    (b : ∀ i, (∂Δ[n + 1] : SSet.{max u v}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) (y i))
    (g : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i))) _⦋n + 1⦌)
    (hb : ∀ i, b i ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) (y i)) =
      (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (g i)) :
    ∃ s' : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x, ∃ R : s' ⟶ s,
      ∃ t : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s'.obj.left) (y i)) _⦋n + 1⦌,
        ∀ i, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofTransportedFiller A D P x (y i) R (b i) (g i) (t i)) := by
  obtain ⟨s', R, t, hF⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofFinite_exists_relativeFillerData A D P hP x y s b g hb
  refine ⟨s', R, t, ?_⟩
  intro i
  let F := Classical.choice (hF i)
  exact ⟨⟨F, F.transportTriangle A D P hP x (y i)⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
