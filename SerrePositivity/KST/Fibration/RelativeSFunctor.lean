module
public import SerrePositivity.KST.Fibration.RelativeSQuotient

/-! # 相対 S• の包含側の関手性

完全関手 A → B と商 B → C に対し、wS•(A, qf) → wS•(B, q) を構成する。
全 Ar 成分を保持し、面・退化および元の core からの包含と厳密に可換にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 完全関手は、合成した商に対する相対条件を元の商の相対条件へ写す。 -/
def relativeSFunctorMap {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {C : SSet.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : B.obj ⟶ C) (n : ℕ) :
    (relativeSConstruction (f.hom ≫ q) n : SSet.{u}) ⟶
      (relativeSConstruction q n : SSet.{u}) :=
  relativeDiagramMap q (fun a => sComponentEvaluation A.obj n a ≫ f.hom)
    (sComponentEvaluation B.obj n) (sPostcomp n f.hom (exactMap_preservesSData f)) id
    (fun a => sPostcomp_gapped_evaluate n f.hom (exactMap_preservesSData f) a)

/-- 相対関手の包含後は、元の S_n の完全関手による後合成である。 -/
lemma relativeSFunctorMap_ι {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {C : SSet.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : B.obj ⟶ C) (n : ℕ) :
    relativeSFunctorMap f q n ≫ (relativeSConstruction q n).ι =
      (relativeSConstruction (f.hom ≫ q) n).ι ≫
        sPostcomp n f.hom (exactMap_preservesSData f) := rfl

/-- 包含側の相対関手は全ての面・退化と可換。 -/
def relativeSimplicialFunctorMap {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {C : SSet.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : B.obj ⟶ C) :
    relativeSimplicialSConstruction (f.hom ≫ q) ⟶ relativeSimplicialSConstruction q where
  app n := relativeSFunctorMap f q n.unop.len
  naturality {n m} θ := by
    apply (cancel_mono (relativeSConstruction q m.unop.len).ι).1
    simp only [Category.assoc, relativeSFunctorMap_ι]
    change relativeDiagramMap (f.hom ≫ q)
        (sComponentEvaluation A.obj n.unop.len) (sComponentEvaluation A.obj m.unop.len)
        (sMap A.obj θ.unop.toOrderHom) (arVertexFunctor.map θ.unop)
        (sComponentEvaluation_reindex A.obj θ) ≫
          (relativeSConstruction (f.hom ≫ q) m.unop.len).ι ≫ _ =
      relativeSFunctorMap f q n.unop.len ≫ relativeDiagramMap q
        (sComponentEvaluation B.obj n.unop.len) (sComponentEvaluation B.obj m.unop.len)
        (sMap B.obj θ.unop.toOrderHom) (arVertexFunctor.map θ.unop)
        (sComponentEvaluation_reindex B.obj θ) ≫ _
    dsimp only [relativeSConstruction]
    rw [← Category.assoc, relativeDiagramMap_ι, Category.assoc, relativeDiagramMap_ι]
    change _ = relativeSFunctorMap f q n.unop.len ≫ (relativeSConstruction q n.unop.len).ι ≫ _
    have he := congrArg (fun a => a ≫ sMap B.obj θ.unop.toOrderHom)
      (relativeSFunctorMap_ι f q n.unop.len)
    simp only [Category.assoc] at he ⊢
    rw [he, exactSPostcomp_reindex]
    rfl

/-- 各段の core からの包含と相対関手は、元の完全関手の core 化と可換。 -/
lemma relativeSFunctorMap_core {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {C : SSet.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : B.obj ⟶ C) (n : ℕ) :
    relativeDiagramCoreInclusion (f.hom ≫ q) (sComponentEvaluation A.obj n) ≫
      relativeSFunctorMap f q n =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sPostcomp n f.hom (exactMap_preservesSData f)) ≫
          relativeDiagramCoreInclusion q (sComponentEvaluation B.obj n) :=
  relativeDiagramCoreInclusion_naturality q
    (fun a => sComponentEvaluation A.obj n a ≫ f.hom) (sComponentEvaluation B.obj n)
    (sPostcomp n f.hom (exactMap_preservesSData f)) id
    (fun a => sPostcomp_gapped_evaluate n f.hom (exactMap_preservesSData f) a)

end SerrePositivity.KST.Fibration
