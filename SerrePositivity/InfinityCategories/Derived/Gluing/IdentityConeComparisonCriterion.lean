module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LocalizationProjectionComparison
public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxVerdier
public import SerrePositivity.InfinityCategories.Stable.EquivalenceStability
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
/-!
概要：同じ恒等 lax 比較に沿って、対角零化と実右軸の全比較から cone 関手を同定する。
方針：指定同値の実逆で関手を運び、恒等 lax 局所化を右軸で試験し、往復則で戻す。
規約：全関手同型と元の選択差を保持。使われ方：恒等 cone 比較の一般判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open SerrePositivity.KST.LocalizingInvariants
open scoped _root_.Simplicial
variable (C : StableCategory.{u}) {G P : SSet.{u}}
  [Quasicategory G] [Quasicategory P] [IsStable G] [IsStable P]
local notation "L" => StableCategory.obj (laxCategory (𝟙 C) (𝟙 C))
local notation "δ" => ExactMap.hom (exactLaxDifference (𝟙 C) (𝟙 C))
local notation "d" => ExactMap.hom (IdentityLax.exactDiagonal C)

def identityConeComparisonCriterion (e : QCatEquivalence G L)
    (y : QCatEquivalence C.obj P) (f : G ⟶ P) [IsExactFunctor f]
    (i j : C.obj ⟶ G)
    (hi : FunctorIso (i ≫ e.hom) d)
    (hj : FunctorIso ((j ≫ e.hom) ≫ δ) (𝟙 C.obj))
    (hf : FunctorIso y.hom (j ≫ f))
    (hz : ∀ x, IsZeroVertex ((i ≫ f).app (Opposite.op ⦋0⦌) x)) :
    FunctorIso ((e.hom ≫ δ) ≫ y.hom) f := by
  let r := e.inv ≫ f ≫ y.inv
  let k := j ≫ e.hom
  letI : IsExactFunctor e.inv := isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  letI : IsExactFunctor y.inv := isExactFunctor_of_isQCatEquivalence y.symm.isQCatEquivalence
  letI : IsExactFunctor (f ≫ y.inv) := isExactFunctor_comp _ _
  letI : IsExactFunctor r := isExactFunctor_comp _ _
  let re : ExactMap (laxCategory (𝟙 C) (𝟙 C)) C := ⟨r, inferInstance⟩
  have hdi₁ : FunctorIso (d ≫ r) (i ≫ e.hom ≫ e.inv ≫ f ≫ y.inv) := by
    simpa only [FunctorIso, r, Category.assoc] using FunctorIso.postcomp hi.symm r
  have hdi₂ : FunctorIso (i ≫ e.hom ≫ e.inv ≫ f ≫ y.inv) (i ≫ f ≫ y.inv) := by
    simpa only [FunctorIso, Category.assoc, Category.comp_id] using
      (e.homInvIso.precomp i).postcomp (f ≫ y.inv)
  have hzero : ∀ x, IsZeroVertex ((d ≫ r).app (Opposite.op ⦋0⦌) x) := by
    intro x
    have hx := IsExactFunctor.preservesZero (F := y.inv) _ (hz x)
    exact hx.of_vertexIso (FunctorIso.app (hdi₁.trans hdi₂) x).symm
  have hk₁ : FunctorIso (k ≫ r) (j ≫ f ≫ y.inv) := by
    simpa only [FunctorIso, k, r, Category.assoc, Category.comp_id] using
      (e.homInvIso.precomp j).postcomp (f ≫ y.inv)
  have hk₂ : FunctorIso (j ≫ f ≫ y.inv) (𝟙 C.obj) := by
    have h : FunctorIso (j ≫ f ≫ y.inv) (y.hom ≫ y.inv) :=
      F2.functorIsoOfEq (FunctorIso.postcomp hf.symm y.inv) (Category.assoc _ _ _) rfl
    exact h.trans y.homInvIso
  have htest : FunctorIso (k ≫ r) (k ≫ δ) := hk₁.trans (hk₂.trans hj.symm)
  have heq : IsQCatEquivalence (k ≫ δ) :=
    (QCatEquivalence.refl C.obj).isQCatEquivalence.ofFunctorIso hj.symm
  have hrd : FunctorIso r δ := localizationProjectionComparisonOfTest δ
    (cofiberLocalizingEdges (essentialImage (IdentityLax.exactDiagonal C)))
    (IdentityLax.difference_isVerdier C).quotient k heq r
    ((inverts_iff_kills_inclusion (IdentityLax.exactDiagonal C) re).mpr hzero) htest
  have hout : FunctorIso (e.hom ≫ r ≫ y.hom) ((e.hom ≫ δ) ≫ y.hom) := by
    simpa only [FunctorIso, Category.assoc] using (hrd.precomp e.hom).postcomp y.hom
  have hcancel₁ : FunctorIso (e.hom ≫ r ≫ y.hom) (f ≫ y.inv ≫ y.hom) := by
    simpa only [FunctorIso, r, Category.assoc, Category.id_comp] using
      e.homInvIso.postcomp (f ≫ y.inv ≫ y.hom)
  have hcancel₂ : FunctorIso (f ≫ y.inv ≫ y.hom) f := by
    simpa only [FunctorIso, Category.assoc, Category.comp_id] using y.invHomIso.precomp f
  exact hout.symm.trans (hcancel₁.trans hcancel₂)

end SerrePositivity.InfinityCategories
