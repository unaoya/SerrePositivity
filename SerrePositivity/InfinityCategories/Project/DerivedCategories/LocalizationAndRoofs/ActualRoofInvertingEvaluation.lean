module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.ActualRoofComposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization

/-! # 反転関手による実屋根の値と実合成三角形

概要：反転関手の下で屋根の値を実辺として取り、実屋根合成が実合成三角形へ写ることを示す。
方針：可逆な分母を消去して値を選び、四つの実三角形の像を同じ合成辺へ照合する。
規約：標的は任意の quasicategory。全高次の結合整合性はまだ主張しない。
使われ方：任意標的への商 Hom 作用と実屋根の合成の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 反転関手の下での実屋根の値と、分母による評価の実三角形。 -/
structure ActualRoofEvaluation {X Y : SSet.{u}} {W : Set (X _⦋1⦌)} {x y : X _⦋0⦌}
    (F : X ⟶ Y) (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ActualRoofSpan W x y) where
  value : Truncated.Edge (X := (truncation 2).obj Y)
    (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y)
  triangle : Truncated.Edge.CompStruct (r.denominator.map ((truncation 2).map F)) value
    (r.numerator.map ((truncation 2).map F))

/-- 反転関手による、実屋根分母の実際の像は可逆。 -/
lemma actualRoofMappedDenominator_isInvertible {X Y : SSet.{u}}
    {W : Set (X _⦋1⦌)} (F : X ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) {x y : X _⦋0⦌}
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ActualRoofSpan W x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := Y) (r.denominator.map ((truncation 2).map F)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := Y) (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex r.denominator.edge).map
    ((truncation 2).map F)) (f := r.denominator.map ((truncation 2).map F)) rfl).mp
      (hF r.denominator_mem)

/-- 任意の反転関手の下で、各実屋根は評価三角形を持つ実辺の値を持つ。 -/
theorem actualRoofEvaluation_nonempty {X Y : SSet.{u}} [Quasicategory Y]
    {W : Set (X _⦋1⦌)} (F : X ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) {x y : X _⦋0⦌}
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ActualRoofSpan W x y) : Nonempty (ActualRoofEvaluation F r) := by
  let d := Truncated.HomotopyCategory.homMk (r.denominator.map ((truncation 2).map F))
  have : IsIso d := actualRoofMappedDenominator_isInvertible F hF r
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y)
    (inv d ≫ Truncated.HomotopyCategory.homMk (r.numerator.map ((truncation 2).map F)))
  have ht : Nonempty (Truncated.Edge.CompStruct
      (r.denominator.map ((truncation 2).map F)) e
      (r.numerator.map ((truncation 2).map F))) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac
    rw [he, ← Category.assoc]
    simpa only [d, Category.assoc] using IsIso.hom_inv_id_assoc d
      (Truncated.HomotopyCategory.homMk (r.numerator.map ((truncation 2).map F)))
  exact ⟨⟨e, ht.some⟩⟩

/-- 合成屋根の任意の評価辺は、元の二評価辺と実際の合成三角形をなす。 -/
theorem actualRoofEvaluation_compositionTriangle_nonempty {X Y : SSet.{u}}
    [Quasicategory Y] {W : Set (X _⦋1⦌)} (F : X ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W)
    {x y z : X _⦋0⦌} {r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ActualRoofSpan W x y} {s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ActualRoofSpan W y z}
    (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ActualRoofComposition W r s) (er : ActualRoofEvaluation F r)
    (es : ActualRoofEvaluation F s) (ec : ActualRoofEvaluation F C.composite) :
    Nonempty (Truncated.Edge.CompStruct er.value es.value ec.value) := by
  let κ := (truncation 2).map F
  have hd := Truncated.HomotopyCategory.homMk_comp_homMk (C.denominatorTriangle.map κ)
  have hn := Truncated.HomotopyCategory.homMk_comp_homMk (C.numeratorTriangle.map κ)
  have ho₁ := Truncated.HomotopyCategory.homMk_comp_homMk (C.firstTriangle.map κ)
  have ho₂ := Truncated.HomotopyCategory.homMk_comp_homMk (C.secondTriangle.map κ)
  have hr := Truncated.HomotopyCategory.homMk_comp_homMk er.triangle
  have hs := Truncated.HomotopyCategory.homMk_comp_homMk es.triangle
  have hc := Truncated.HomotopyCategory.homMk_comp_homMk ec.triangle
  have : IsIso (Truncated.HomotopyCategory.homMk (C.combinedDenominator.map κ)) :=
    actualRoofMappedDenominator_isInvertible F hF C.composite
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac
  apply (cancel_epi (Truncated.HomotopyCategory.homMk (C.combinedDenominator.map κ))).mp
  calc
    _ = Truncated.HomotopyCategory.homMk (C.denominator.map κ) ≫
        Truncated.HomotopyCategory.homMk (r.numerator.map κ) ≫
        Truncated.HomotopyCategory.homMk es.value := by
      rw [← hd]
      simpa only [Category.assoc] using congrArg
        (fun v => Truncated.HomotopyCategory.homMk (C.denominator.map κ) ≫ v ≫
          Truncated.HomotopyCategory.homMk es.value) hr
    _ = Truncated.HomotopyCategory.homMk (C.lift.map κ) ≫
        Truncated.HomotopyCategory.homMk (s.denominator.map κ) ≫
        Truncated.HomotopyCategory.homMk es.value := by
      rw [← Category.assoc, ho₁, ← ho₂, Category.assoc]
    _ = Truncated.HomotopyCategory.homMk (C.combinedNumerator.map κ) := by rw [hs, hn]
    _ = _ := hc.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
