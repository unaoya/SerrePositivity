module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonContraction
public import SerrePositivity.DifferentialGraded.Category.ComplexHomotopyComparison
public import SerrePositivity.DifferentialGraded.Derived.Restriction
public import SerrePositivity.DifferentialGraded.Derived.Evaluation
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology

/-! # dg 商の加群を制限したときの S 上の acyclic 性

商の任意の右 dg 加群は、指定収縮のある対象で acyclic である。
局所 K-flat 仮定が必要となる逆向きの本質像判定は、この零性と区別する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex Opposite
variable (A : Type u) [CommRing A]

lemma complex_acyclic_of_homotopy_isZero (K : Complex A)
    (hK : IsZero ((toHomotopy A (Complex A)).obj (ForgetEnrichment.of (Complex A) K))) :
    K.Acyclic := by
  have hQ : IsZero ((_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj K) :=
    (complexHomotopyComparison A).map_isZero hK
  intro n
  apply (exactAt_iff_isZero_homology K n).2
  have hH := (_root_.HomotopyCategory.homologyFunctor (ModuleCat.{u} A) (.up ℤ) n).map_isZero hQ
  exact hH.of_iso ((_root_.HomotopyCategory.homologyFunctorFactors
    (ModuleCat.{u} A) (.up ℤ) n).app K).symm

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 右加群は、商内で指定収縮を持つ各対象に acyclic 複体を割り当てる。 -/
lemma quotientModule_value_acyclic (S : Set D) (M : RightModule A (QuotientObject D S)) (b : S) :
    (M.obj (op (⟨b.val⟩ : QuotientObject D S))).Acyclic := by
  have hb : IsZero ((toHomotopy A (QuotientObject D S)ᵒᵖ).obj
      (ForgetEnrichment.of (Complex A) (op (⟨b.val⟩ : QuotientObject D S)))) :=
    homotopy_isZero_of_unit_boundary A (QuotientObject D S)ᵒᵖ (op ⟨b.val⟩)
      (epsilonElement A D S b) (differential_epsilonElement A D S b)
  exact complex_acyclic_of_homotopy_isZero A _ (M.toFunctor.onHomotopy.map_isZero hb)

/-- 閉零の制限関手の本質像は S 上で objectwise acyclic。 -/
lemma quotientModuleRestriction_value_acyclic (S : Set D)
    (M : ModuleCategory A (QuotientObject D S)) (b : S) :
    ((moduleEvaluation A D b.val).obj
      ((moduleRestriction A D (QuotientObject D S) (inclusion A D S).op).obj M)).Acyclic :=
  quotientModule_value_acyclic A D S (ForgetEnrichment.to (Complex A) M) b

/-- 導来制限の像も S 上の全ホモロジーが零である。置換や平坦性は不要。 -/
lemma quotientDerivedRestriction_homology_isZero (S : Set D)
    (X : DerivedModuleCategory A (QuotientObject D S)) (b : S) (n : ℤ) :
    IsZero ((moduleDerivedHomology A D b.val n).obj
      ((dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj X)) := by
  obtain ⟨⟨M⟩⟩ := X
  have hR := congrArg (fun G => G.obj M)
    (dgDerivedRestriction_fac A D (QuotientObject D S) (inclusion A D S))
  change IsZero ((moduleDerivedHomology A D b.val n).obj
    ((moduleToDerived A (QuotientObject D S) ⋙
      dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj M))
  rw [hR]
  let N := (moduleRestriction A D (QuotientObject D S) (inclusion A D S).op).obj M
  have hH := congrArg (fun G => G.obj N) (moduleDerivedHomology_fac A D b.val n)
  change IsZero ((moduleToDerived A D ⋙ moduleDerivedHomology A D b.val n).obj N)
  rw [hH]
  exact (quotientModuleRestriction_value_acyclic A D S M b n).isZero_homology

/-- S の代表加群から導来制限の像への射は零だけである。 -/
lemma quotientDerivedRestriction_representable_hom_subsingleton (S : Set D)
    (X : DerivedModuleCategory A (QuotientObject D S)) (b : S) :
    Subsingleton ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A b.val)) ⟶
        (dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj X) := by
  have h : Subsingleton ((moduleDerivedHomology A D b.val 0).obj
      ((dgDerivedRestriction A D (QuotientObject D S) (inclusion A D S)).obj X)) :=
    ModuleCat.isZero_iff_subsingleton.mp (quotientDerivedRestriction_homology_isZero A D S X b 0)
  exact (moduleRepresentableDerivedHomEquiv A D b.val _).injective.subsingleton

end SerrePositivity.DifferentialGraded.DGQuotient
