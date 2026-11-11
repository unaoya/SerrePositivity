module
public import SerrePositivity.KST.Fibration.RelativeSKernelContraction

/-! # 核上の相対 S• と元の全 S• の、包含をそのまま保持する単体的同型 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 全体と等しい実部分複体の同型の順射は、同じ元の包含そのもの。 -/
theorem subcomplexTopIso_hom_inclusion {X : SSet.{u}} (P : X.Subcomplex) (h : P = ⊤) :
    (eqToIso (congrArg (fun Q : X.Subcomplex => (Q : SSet.{u})) h) ≪≫
      Subcomplex.topIso X).hom = P.ι := by
  subst P
  rfl

/-- 元の核の各相対 S_n の同型は、周囲の元の S_n への包含を厳密に回収する。 -/
theorem relativeSKernelTopIso_hom_inclusion
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ) :
    (relativeSKernelTopIso h n).hom = (relativeSConstruction (i.hom ≫ q.hom) n).ι :=
  subcomplexTopIso_hom_inclusion _ (relativeSKernel_eq_top h n)

/-- 元の各段の同型は、全ての面・退化と厳密に可換する。 -/
theorem relativeSKernelTopIso_naturality
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    (relativeSimplicialSConstruction (i.hom ≫ q.hom)).map θ ≫
        (relativeSKernelTopIso h m.unop.len).hom =
      (relativeSKernelTopIso h n.unop.len).hom ≫ (simplicialSConstruction A.obj).map θ := by
  rw [relativeSKernelTopIso_hom_inclusion, relativeSKernelTopIso_hom_inclusion]
  rfl

/-- 元の相対 S 核の同じ全単体的図式は、元の全 S• と自然に同型。 -/
def relativeSKernelSimplicialIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    relativeSimplicialSConstruction (i.hom ≫ q.hom) ≅ simplicialSConstruction A.obj :=
  NatIso.ofComponents (fun n => relativeSKernelTopIso h n.unop.len)
    (fun θ => relativeSKernelTopIso_naturality h θ)

end SerrePositivity.KST.Fibration
