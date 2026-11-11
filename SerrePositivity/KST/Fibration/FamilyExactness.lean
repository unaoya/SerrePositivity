module
public import SerrePositivity.KST.Fibration.CofiberFamilyUntranspose
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorChoice
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TrivialFibrationSquares

/-! # 族の完全性の点ごとの判定と cofiber 射影による反映

元の関手圏の普遍性と自明 Kan 射影を使い、cofiber 図式値の完全関手を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 関手圏に値を持つ族の完全性は、全ての頂点評価から従う。 -/
lemma preservesCofiberData_of_evaluations {A K : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : A ⟶ (ihom K).obj B.obj)
    (hf : ∀ k : K _⦋0⦌, PreservesCofiberData (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)) :
    PreservesCofiberData f := by
  constructor
  · intro z hz
    apply isZeroVertex_of_pointwise
    intro k
    exact (hf k).1 z hz
  · intro t ht
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPushoutSquare_of_pointwise
    intro k
    simpa only [Category.assoc] using (hf k).2 t ht

/-- 射の族は両端の評価が完全なら完全である。 -/
lemma preservesCofiberData_arrow_of_endpoints {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : A ⟶ (ihom (Δ[1] : SSet.{u})).obj B.obj)
    (h₀ : PreservesCofiberData (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (h₁ : PreservesCofiberData (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) :
    PreservesCofiberData f := by
  apply preservesCofiberData_of_evaluations
  intro a
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
  fin_cases j
  · exact h₀
  · exact h₁

/-- 自明 Kan 射影との合成の完全性は、元の族へ反映される。 -/
lemma preservesCofiberData_of_trivialProjection {A E Y : SSet.{u}}
    [Quasicategory E] [Quasicategory Y] (p : E ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (f : A ⟶ E) (hf : PreservesCofiberData (f ≫ p)) : PreservesCofiberData f := by
  constructor
  · intro z hz
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isZeroVertex_iff_map_of_trivialKanFibration p _).2 (hf.1 z hz)
  · intro t ht
    apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_iff_postcomp_trivialKanFibration p _).2
    simpa only [Category.assoc] using hf.2 t ht

/-- 全 cofiber 四角形の族は、始点・中間頂点の二評価が完全なら完全である。 -/
lemma cofiberFamily_preservesCofiberData_of_endpoints {A : SSet.{u}}
    {B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : A ⟶ cofiberDiagrams B.obj)
    (h₀ : PreservesCofiberData (f ≫ (cofiberStableSubobject (sInputModel B)).val))
    (h₁ : PreservesCofiberData (f ≫ (cofiberStableMiddle (sInputModel B)).val)) :
    PreservesCofiberData f := by
  apply preservesCofiberData_of_trivialProjection (cofiberProjection B.obj)
  apply preservesCofiberData_arrow_of_endpoints
  · have he : cofiberProjection B.obj ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        (cofiberStableSubobject (sInputModel B)).val := by
      rw [cofiberProjection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
      rfl
    rw [Category.assoc, he]
    exact h₀
  · have he : cofiberProjection B.obj ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (cofiberStableMiddle (sInputModel B)).val := by
      rw [cofiberProjection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
      rfl
    rw [Category.assoc, he]
    exact h₁

/-- 元の関手頂点の自然同型から、対応する族の完全性を輸送する。 -/
lemma preservesCofiberData_of_familyVertexIso {A : SSet.{u}} [Quasicategory A]
    {B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (v : ((ihom A).obj B.obj) _⦋0⦌) (f : A ⟶ B.obj)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso v (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) (hf : PreservesCofiberData f) :
    PreservesCofiberData ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A B.obj).symm v) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f := ⟨hf.1, hf.2⟩
  have ei : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A B.obj).symm v) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A B.obj)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A B.obj).symm v))
    rw [Equiv.apply_symm_apply]
    exact e.symm
  have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_functorIso ei
  exact ⟨he.preservesZero, he.preservesCofiber⟩

end SerrePositivity.KST.Fibration
