module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDoldKanHomDiagram
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGStandardClosedPrecomposition
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ComplexPinchedPrecomposition

/-!
概要：指定Γ Hom同型は同じ閉射の実豊穣前合成を保つ。
方針：標準成分への鎖作用を既存の前合成則と同定し、Γ同型の全鎖射自然性を使う。
規約：IS-W2 D01の既存構成の前合成・係数移送則。全単体を保つ。
使われ方：HA 1.2.4、点ごとのBK錐と元の実豊穣Homの前合成の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]

/-- 同じ標準鎖作用は元の閉前合成の全単体作用そのもの。 -/
theorem standardChainMap_closedPrecomposition (x y z : D)
    (f : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y) :
    Functor.whiskerRight
      (_root_.SerrePositivity.ComplexLimits.standardModuleChainMap
        (eHomWhiskerRight (Complex R) f (ForgetEnrichment.of (Complex R) z)))
      (forget (ModuleCat R)) =
    eHomWhiskerRight SSet f (ForgetEnrichment.of (Complex R) z) := by
  rw [dgStandardSimplicialPrecomp_chainMap]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((_root_.SerrePositivity.ComplexLimits.standardModuleChainMap
    (eHomWhiskerRight (Complex R) f (ForgetEnrichment.of (Complex R) z))).app n s).val = _
  rw [_root_.SerrePositivity.ComplexLimits.standardModuleChainMap_val]
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (eHomWhiskerRight (Complex R) f (ForgetEnrichment.of (Complex R) z)).f k
    (s.val.component J k hJ hk) =
      (dgStandardSimplexMap
        (eHomWhiskerRight (Complex R) f (ForgetEnrichment.of (Complex R) z)) s).val.component
        J k hJ hk
  rw [dgStandardSimplexMap_component]

/-- 指定Γ Hom同型は元の閉前合成とsmart切断の全像に自然。 -/
theorem doldKanSimplicialHomIso_precomposition (x y z : D)
    (f : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y) :
    eHomWhiskerRight SSet f (ForgetEnrichment.of (Complex R) z) ≫
        (doldKanSimplicialHomIso (R := R) x z).hom =
      (doldKanSimplicialHomIso (R := R) y z).hom ≫
        Functor.whiskerRight
          ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat R) ℕ ⥤ SimplicialObject (ModuleCat R)).map
            (truncLE'Map (eHomWhiskerRight (Complex R) f (ForgetEnrichment.of (Complex R) z))
              (ComplexShape.embeddingUpIntLE 0))) (forget (ModuleCat R)) := by
  rw [← standardChainMap_closedPrecomposition]
  exact congrArg (fun g => Functor.whiskerRight g (forget (ModuleCat R)))
    (_root_.SerrePositivity.ComplexLimits.standardDoldKanModuleIso_chainMap
      (eHomWhiskerRight (Complex R) f (ForgetEnrichment.of (Complex R) z)))

/-- 元の複体射の指定Γ Hom比較は、元の豊穣前合成を厳密に保つ。 -/
theorem complexDoldKanHomIso_precomposition {A : Type u} [CommRing A]
    {P Q : Complex A} (f : P ⟶ Q) (T : Complex A) :
    eHomWhiskerRight SSet ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f)
        (ForgetEnrichment.of (Complex A) T) ≫ (complexDoldKanHomIso A P).hom.app T =
      (complexDoldKanHomIso A Q).hom.app T ≫
        Functor.whiskerRight
          ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤ SimplicialObject (ModuleCat A)).map
            (truncLE'Map (homPrecompose f T) (ComplexShape.embeddingUpIntLE 0)))
          (forget (ModuleCat A)) := by
  have h := doldKanSimplicialHomIso_precomposition A (Complex A) P Q T
    ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f)
  rw [_root_.SerrePositivity.ComplexLimits.complexToClosed_precomposition] at h
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
