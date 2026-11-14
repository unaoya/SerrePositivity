module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.DGCoherentSliceComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHomComposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionPrism

/-! # 実 dg pinched Hom の全合成 prism

概要：標準豊穣合成を F1 の prism と比較写像で実 dg nerve の slice へ戻す。
方針：既存の全次数の等式を同じ写像のまま接続する。
規約：有限性・前三角性を仮定しない。使われ方：実屋根の四三角形の高次の族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- coherent nerve の豊穣合成は、標準同型で移すと実 AW 合成に一致する。 -/
lemma dgCoherentHomComposition (x y z : D) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x y).inv ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) y z).inv) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComposition (ForgetEnrichment.of (Complex A) x)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x z).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition (A := A) x y z := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨f, g⟩
  rfl
/-- 全ての実 Hom 単体対を同時に扱う、実 dg target slice 内の合成 prism。 -/
def dgPinchedCompositionPrism (x y z : D) :
    (Δ[1] : SSet.{max u v}) ⊗ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z)) :=
  (Δ[1] ◁ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x y).inv ⊗ₘ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) y z).inv)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionPrism (ForgetEnrichment.of (Complex A) x)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentTargetSliceMap A D z
/-- 実合成 prism の零端は、同じ実 AW 合成の slice 表示。 -/
lemma dgPinchedCompositionPrism_zero (x y z : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ dgPinchedCompositionPrism A D x y z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition (A := A) x y z ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D x z := by
  let ψ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x y).inv ⊗ₘ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) y z).inv
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionPrism_zero (C := ClosedCategory A D)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z)
  have ht := congrArg (fun k => ψ ≫ k ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentTargetSliceMap A D z) hp
  dsimp only [dgPinchedCompositionPrism]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality]
  simp only [Category.assoc] at ht ⊢
  refine ht.trans ?_
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentHomComparison_slice A D
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z)
  have hst := congrArg (fun k => ψ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComposition
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) ≫ k) hs
  refine hst.trans ?_
  exact congrArg (fun k => k ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D x z)
    (dgCoherentHomComposition A D x y z)
/-- 実合成 prism の一端は、指定第二射の slice 表示。 -/
lemma dgPinchedCompositionPrism_one (x y z : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ dgPinchedCompositionPrism A D x y z =
      snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D y z := by
  let ψ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x y).inv ⊗ₘ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) y z).inv
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionPrism_one (C := ClosedCategory A D)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z)
  have ht := congrArg (fun k => ψ ≫ k ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentTargetSliceMap A D z) hp
  dsimp only [dgPinchedCompositionPrism]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality]
  simp only [Category.assoc] at ht ⊢
  refine ht.trans ?_
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentHomComparison_slice A D
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z)
  have hst := congrArg (fun k => ψ ≫ snd _ _ ≫ k) hs
  refine hst.trans ?_
  have hc : ψ ≫ snd _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) y z).hom =
      snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) := by
    dsimp only [ψ]
    rw [tensorHom_snd_assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun k => k ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D y z) hc

end SerrePositivity.InfinityCategories.Project.DerivedCategories
