module
public import SerrePositivity.KST.Fibration.CoreFactorization

/-! # 内 anodyne 制限による元の安定圏内の全可逆単体の反映

同じ制限の二つの図式を全関手圏内で同型とし、元の閉じた W 条件へ反映する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 内 anodyne 制限後に core を通る元の単体図式は、制限前から core を通る。 -/
lemma coreFactor_of_innerAnodyne {K : SSet.{u}} {C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (n : SimplexCategory) (i : K ⟶ stdSimplex.obj n) (hi : innerAnodyneExtensions i)
    (f : stdSimplex.obj n ⟶ C.obj)
    (hf : ∃ g : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj : SSet.{u}),
      g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι = i ≫ f) :
    ∃ g : stdSimplex.obj n ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj : SSet.{u}),
      g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι = f := by
  obtain ⟨g, hg⟩ := hf
  obtain ⟨G, hG⟩ := exists_extension_of_innerAnodyne i hi g
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre i).app C.obj) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne i hi C.obj
  have he : ((pre i).app C.obj).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (G ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι)) =
        ((pre i).app C.obj).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ (G ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ f)
    rw [← Category.assoc, hG, hg]
  let e := vertexIsoOfTrivialKanFibrationEq ((pre i).app C.obj) _ _ he
  have hclosed : (weakStringClosedPredicate (𝟙 C) n).predicate
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (G ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι)) :=
    (weakStringPredicate_functorVertex_iff_factorCore (𝟙 C) n _).2
      ⟨G, by
        change G ≫ _ = (G ≫ _) ≫ 𝟙 C.obj
        rw [Category.comp_id]⟩
  have hfinal := (weakStringClosedPredicate (𝟙 C) n).of_iso hclosed e
  obtain ⟨H, hH⟩ := (weakStringPredicate_functorVertex_iff_factorCore (𝟙 C) n f).1 hfinal
  change H ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι = f ≫ 𝟙 C.obj at hH
  exact ⟨H, by simpa only [Category.comp_id] using hH⟩

end SerrePositivity.KST.Fibration
