module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLengthModule
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltrationZero
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonContraction
public import SerrePositivity.DifferentialGraded.Module.RestrictionRepresentable
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects

/-! # 長さ零段階と代表加群、および商への比較射

元の Hom と零段階の同型を、全次数自然な加群同型へ持ち上げる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
private lemma family_naturality_of_injective
    {M N T : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ⟶ N.obj x)
    (j : ∀ x : Dᵒᵖ, N.obj x ⟶ T.obj x)
    (b : ∀ x : Dᵒᵖ, M.obj x ⟶ T.obj x)
    (hj : ∀ x i, Function.Injective ((j x).f i))
    (hfac : ∀ x, a x ≫ j x = b x)
    (hn : ∀ x y, N.map x y ≫ homPostcompose (N.obj x) (j y) =
      T.map x y ≫ homPrecompose (j x) (T.obj y))
    (hb : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (b y) =
      T.map x y ≫ homPrecompose (b x) (T.obj y)) (x y : Dᵒᵖ) :
    M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y) := by
  apply closedFamily_of_action A (M := M) (N := N) a
  intro x y p i k hik f t
  apply hj y k
  have hx := congrArg (fun g => g.f i t) (hfac x)
  have hy := congrArg (fun g => g.f k (moduleAction A M f t hik)) (hfac y)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hx hy
  rw [hy, closedFamily_action A j hn, hx]
  exact closedFamily_action A b hb x y p i k hik f t

lemma lengthZeroModule_naturality (S : Set D) (z : D) (x y : Dᵒᵖ) :
    (representable A z).map x y ≫ homPostcompose (homObject A D x.unop z)
        (lengthZeroMap A D S y.unop z) =
      (lengthModule A D S z 0).map x y ≫ homPrecompose (lengthZeroMap A D S x.unop z)
        (lengthComplex A D S y.unop z 0) := by
  exact family_naturality_of_injective A D
    (M := representable A z) (N := lengthModule A D S z 0)
    (T := quotientRepresentableRestriction A D S z)
    (fun x => lengthZeroMap A D S x.unop z)
    (fun x => lengthInclusion A D S x.unop z 0)
    (fun x => originalHomInclusion A D S x.unop z)
    (fun _ _ => Subtype.val_injective)
    (fun x => lengthZeroMap_inclusion A D S x.unop z)
    (lengthModuleMap_inclusion A D S z 0)
    (representableRestriction_naturality A D (QuotientObject D S) (inclusion A D S) z) x y

/-- 元の代表加群から長さ零段階への実際の閉零射。 -/
def lengthZeroModuleMap (S : Set D) (z : D) :
    ForgetEnrichment.of (Complex A) (representable A z) ⟶
      ForgetEnrichment.of (Complex A) (lengthModule A D S z 0) :=
  moduleMorphismMk A D (fun x => lengthZeroMap A D S x.unop z)
    (lengthZeroModule_naturality A D S z)

@[simp] lemma lengthZeroModuleMap_eval (S : Set D) (z x : D) :
    (moduleEvaluation A D x).map (lengthZeroModuleMap A D S z) = lengthZeroMap A D S x z :=
  moduleMorphismMk_eval A D _ _ x

instance lengthZeroModuleMap_isIso (S : Set D) (z : D) :
    IsIso (lengthZeroModuleMap A D S z) :=
  moduleIsIso_of_evaluations A D _ (fun x => by
    rw [lengthZeroModuleMap_eval]
    infer_instance)

/-- 零段階は元の代表加群と、加群圏内で同型である。 -/
def lengthZeroModuleIso (S : Set D) (z : D) :
    ForgetEnrichment.of (Complex A) (representable A z) ≅
      ForgetEnrichment.of (Complex A) (lengthModule A D S z 0) :=
  asIso (lengthZeroModuleMap A D S z)

/-- 零段階の包含は、dg 関手の Hom 写像による代表加群の比較そのものである。 -/
@[reassoc] lemma lengthZeroModuleMap_inclusion (S : Set D) (z : D) :
    lengthZeroModuleMap A D S z ≫ lengthModuleInclusion A D S z 0 =
      representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, lengthZeroModuleMap_eval, lengthModuleInclusion_eval,
    representableRestrictionMap_eval]
  exact lengthZeroMap_inclusion A D S x z

end SerrePositivity.DifferentialGraded.DGQuotient
