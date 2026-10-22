module
public import SerrePositivity.KST.Fibration.WeakStringPostcomposition

/-! # 元の全 W 列の後合成と全面・全退化の厳密な可換性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の全関手圏の前合成・後合成の可換性を W 条件への制限が保つ。 -/
lemma weakStringPostMap_reindex {A B C : StableCategory.{u}}
    (f : ExactMap A B) (q : ExactMap B C) {m n : SimplexCategory} (θ : m ⟶ n) :
    weakStringPostMap f q n ≫ weakStringMap q θ =
      weakStringMap (f ≫ q : A ⟶ C) θ ≫ weakStringPostMap f q m := by
  apply (cancel_mono (fullSubcomplexOnVertices _ (weakStringPredicate q m)).ι).1
  calc
    _ = weakStringPostMap f q n ≫
        ((fullSubcomplexOnVertices _ (weakStringPredicate q n)).ι ≫
          (pre (stdSimplex.map θ)).app B.obj) := by
      rw [Category.assoc, weakStringMap_ι]
    _ = (fullSubcomplexOnVertices _ (weakStringPredicate (f ≫ q : A ⟶ C) n)).ι ≫
        ((ihom (stdSimplex.obj n)).map f.hom ≫ (pre (stdSimplex.map θ)).app B.obj) := by
      rw [← Category.assoc, weakStringPostMap_ι, Category.assoc]
    _ = (fullSubcomplexOnVertices _ (weakStringPredicate (f ≫ q : A ⟶ C) n)).ι ≫
        ((pre (stdSimplex.map θ)).app A.obj ≫ (ihom (stdSimplex.obj m)).map f.hom) :=
      congrArg (fun k => (fullSubcomplexOnVertices _
        (weakStringPredicate (f ≫ q : A ⟶ C) n)).ι ≫ k)
        ((pre (stdSimplex.map θ)).naturality f.hom)
    _ = (weakStringMap (f ≫ q : A ⟶ C) θ ≫
        (fullSubcomplexOnVertices _ (weakStringPredicate (f ≫ q : A ⟶ C) m)).ι) ≫
          (ihom (stdSimplex.obj m)).map f.hom := by
      rw [weakStringMap_ι, Category.assoc]
    _ = _ := by simp only [Category.assoc, weakStringPostMap_ι]

/-- 安定な入力の完全関手としても、後合成は全再添字と厳密に可換。 -/
lemma weakStringPostExact_reindex {A B C : StableCategory.{u}}
    (f : ExactMap A B) (q : ExactMap B C) {m n : SimplexCategory} (θ : m ⟶ n) :
    weakStringPostExact f q n ≫ weakStringExactMap q θ =
      weakStringExactMap (f ≫ q : A ⟶ C) θ ≫ weakStringPostExact f q m :=
  Subtype.ext (weakStringPostMap_reindex f q θ)

/-- 元の包含側の完全関手を、全 W 列の単体的な安定入力の自然変換に束ねる。 -/
def weakStringStablePostcomp {A B C : StableCategory.{u}}
    (f : ExactMap A B) (q : ExactMap B C) :
    weakStringStableSimplicial (f ≫ q : A ⟶ C) ⟶ weakStringStableSimplicial q where
  app n := weakStringPostExact f q n.unop
  naturality {_m _n} θ := (weakStringPostExact_reindex f q θ.unop).symm

end SerrePositivity.KST.Fibration
