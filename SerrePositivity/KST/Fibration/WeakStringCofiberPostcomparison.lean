module
public import SerrePositivity.KST.Fibration.WeakCofiberRawProjection
public import SerrePositivity.KST.Fibration.WeakStringPostcomposition

/-! # 元の選択した全 cofiber 補完の後合成の全関手圏内の比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の全共通 cofiber 補完の二つの後合成は、同じ実底辺を厳密に持つ。 -/
lemma weakStringCofiberPostcomparison_bottom {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    (weakStringPostExact f q n ≫ weakStringCofiberExact q α).val ≫
      weakCofiberRawProjection q =
        (weakStringCofiberExact (f ≫ q : A ⟶ C) α ≫ weakCofiberPostExact f q).val ≫
          weakCofiberRawProjection q := by
  have h₁ : (weakStringPostExact f q n ≫ weakStringCofiberExact q α).val ≫
      weakCofiberRawProjection q =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate (f ≫ q : A ⟶ C) n)).ι ≫
        ((ihom (stdSimplex.obj n)).map f.hom ≫ (pre (stdSimplex.map α)).app B.obj) := by
    change (weakStringPostMap f q n ≫ (weakStringCofiberExact q α).val) ≫ _ = _
    rw [Category.assoc, weakStringCofiberExact_rawProjection, ← Category.assoc,
      weakStringPostMap_ι, Category.assoc]
  have h₂ : (weakStringCofiberExact (f ≫ q : A ⟶ C) α ≫ weakCofiberPostExact f q).val ≫
      weakCofiberRawProjection q =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate (f ≫ q : A ⟶ C) n)).ι ≫
        ((pre (stdSimplex.map α)).app A.obj ≫ (ihom (Δ[1] : SSet.{u})).map f.hom) := by
    change ((weakStringCofiberExact (f ≫ q : A ⟶ C) α).val ≫
      (weakCofiberPostExact f q).val) ≫ _ = _
    rw [Category.assoc, weakCofiberPostExact_rawProjection, ← Category.assoc,
      weakStringCofiberExact_rawProjection, Category.assoc]
  exact h₁.trans ((congrArg (fun g => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _
    (weakStringPredicate (f ≫ q : A ⟶ C) n)).ι ≫ g)
      ((pre (stdSimplex.map α)).naturality f.hom)).trans h₂.symm)

/-- 元の二つの共通補完の後合成は、全入力を保つ実関手圏内の自然同型を持つ。 -/
def weakStringCofiberPostcomparison {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (weakStringPostExact f q n ≫ weakStringCofiberExact q α).val
      (weakStringCofiberExact (f ≫ q : A ⟶ C) α ≫ weakCofiberPostExact f q).val := by
  apply (weakCofiberRawProjection_fullyFaithful q).preimageFunctorIso
  exact eqToIso (congrArg (fun k => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex k))
    (weakStringCofiberPostcomparison_bottom f q α))

/-- 元の全共通核値 cofiber も、元の完全関手と核への後合成に関して自然同型になる。 -/
def weakStringKernelCofiber_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (weakStringPostExact f q n ≫ weakStringKernelCofiber q α).val
      (weakStringKernelCofiber (f ≫ q : A ⟶ C) α ≫ kernelPostExact f q).val := by
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((weakStringPostExact f q n ≫ weakStringCofiberExact q α) ≫
        relativeCofiberQuotient (ClosedStablePredicate.top (sInputModel B))
          (kernelClosedPredicate q)).val
      ((weakStringCofiberExact (f ≫ q : A ⟶ C) α ≫ weakCofiberPostExact f q) ≫
        relativeCofiberQuotient (ClosedStablePredicate.top (sInputModel B))
          (kernelClosedPredicate q)).val :=
    (weakStringCofiberPostcomparison f q α).postcomp
      (relativeCofiberQuotient (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q)).val
  simpa only [weakStringKernelCofiber, Category.assoc, weakCofiberPostExact_quotient] using e

end SerrePositivity.KST.Fibration
