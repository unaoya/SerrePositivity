module
public import SerrePositivity.EInfinity.ComplexLimits.DoldKanGammaChainNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardClosedPostcomposition

/-!
概要：指定 Γ 同型を元の閉射の豊穣後合成と照合する。
方針：既存の鎖写像への自然性を再利用し、標準成分の AW 定数作用と比較する。
規約：全次元の等式であり、元の豊穣 Hom の作用を置き換えない。
使われ方：HA 1.2.4、G10 の点ごとの Γ 図式から native 錐への接続。
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

/-- 元の閉後合成の鎖作用と、同じ豊穣後合成は全単体で一致する。 -/
theorem standardChainMap_closedPostcomposition (x y z : D)
    (f : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z) :
    Functor.whiskerRight
      (SerrePositivity.EInfinity.ComplexLimits.standardModuleChainMap
        (dgClosedPostcomposition R D (x := x) f)) (forget (ModuleCat R)) =
      eHomWhiskerLeft SSet (ForgetEnrichment.of (Complex R) x) f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  erw [dgStandardSimplicialPostcomp_app]
  apply Subtype.ext
  change ((SerrePositivity.EInfinity.ComplexLimits.standardModuleChainMap
    (dgClosedPostcomposition R D (x := x) f)).app n s).val = _
  rw [SerrePositivity.EInfinity.ComplexLimits.standardModuleChainMap_val]
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (dgClosedPostcomposition R D (x := x) f).f k (s.val.component J k hJ hk) =
    (awData (standardConstant (closedHomEquiv R D y z f) n.unop.len).val s.val).component J k hJ hk
  rw [dgClosedPostcomposition_f, awData_closed_post_component]
  rfl

/-- 指定 Γ 同型は、同じ閉射の豊穣後合成と smart 切断の像に自然。 -/
theorem doldKanSimplicialHomIso_postcomposition (x y z : D)
    (f : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z) :
    eHomWhiskerLeft SSet (ForgetEnrichment.of (Complex R) x) f ≫
        (doldKanSimplicialHomIso (R := R) x z).hom =
      (doldKanSimplicialHomIso (R := R) x y).hom ≫
        Functor.whiskerRight
          ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat R) ℕ ⥤ SimplicialObject (ModuleCat R)).map
            (truncLE'Map (dgClosedPostcomposition R D (x := x) f)
              (ComplexShape.embeddingUpIntLE 0))) (forget (ModuleCat R)) := by
  rw [← standardChainMap_closedPostcomposition]
  exact congrArg (fun g => Functor.whiskerRight g (forget (ModuleCat R)))
    (SerrePositivity.EInfinity.ComplexLimits.standardDoldKanModuleIso_chainMap
      (dgClosedPostcomposition R D (x := x) f))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
