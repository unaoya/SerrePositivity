module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredPullbackComparison
public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyCoreCriterion
public import SerrePositivity.KST.LocalizingInvariants.RelativeFunctorCoreRestriction
public import SerrePositivity.KST.Fibration.RelativeFirstRowSimplexQuotient

/-!
概要：回収済みの同じ実余錐円柱を、元の商図式 core の strict 逆像へ戻す。
方針：同じ二脚固定比較による前段反転と固定頂点から、円柱全体の全辺反転を証明する。
規約：円柱・両端・区間を選び直さず、元の第一行単体商の座標で実 prism を保持する。
使われ方：境界輸送を元の relativeFirstRowSimplex とその完成へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}

lemma VerdierFiniteMappingCoconeRecovery.cylinderQuotient_invertsAllEdges
    (r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    InvertsEdges (r.cylinder.homotopy.h ≫
      (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) Set.univ := by
  apply coconeFamily_invertsAllEdges_of_prefix_apex _ (q.hom.app (Opposite.op ⦋0⦌) z)
  · rw [Category.assoc, (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).naturality q.hom,
      ← Category.assoc]
    exact r.cylinderPrefixQuotient_invertsAllEdges
  · have hn : (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom ≫
        evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) =
        evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫ q.hom := rfl
    rw [Category.assoc, hn, ← Category.assoc, r.cylinder.homotopy_apex, SSet.const_comp]

/-- 同じ実余錐円柱そのものを、元の全商図式 core の strict 逆像へ持ち上げる。 -/
def VerdierFiniteMappingCoconeRecovery.relativeCylinder
    (r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    S.toSSet ⊗ (Δ[1] : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.relativeFunctorCore q.hom (join (Δ[n] : SSet.{u}) Δ[0]) : SSet.{u}) :=
  corePreimageLift ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom)
    r.cylinder.homotopy.h (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderQuotient_invertsAllEdges r)

lemma VerdierFiniteMappingCoconeRecovery.relativeCylinder_ι
    (r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.relativeCylinder r) ≫ (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.relativeFunctorCore q.hom (join (Δ[n] : SSet.{u}) Δ[0])).ι =
      r.cylinder.homotopy.h := rfl

lemma VerdierFiniteMappingCoconeRecovery.relativeCylinder_start_ι
    (r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (SSet.ι₀ : S.toSSet ⟶ S.toSSet ⊗ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.relativeCylinder r) ≫
      (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.relativeFunctorCore q.hom (join (Δ[n] : SSet.{u}) Δ[0])).ι =
        S.ι ≫ r.cylinder.whole := r.cylinder.homotopy.h₀

lemma VerdierFiniteMappingCoconeRecovery.relativeCylinder_end_ι
    (r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (SSet.ι₁ : S.toSSet ⟶ S.toSSet ⊗ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.relativeCylinder r) ≫
      (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.relativeFunctorCore q.hom (join (Δ[n] : SSet.{u}) Δ[0])).ι =
        r.cylinder.endCone := r.cylinder.homotopy.h₁

/-- 元の第一行標準単体座標へ戻した、同じ実境界円柱の全 prism。 -/
def VerdierFiniteMappingCoconeRecovery.simplexCylinder
    (r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    S.toSSet ⊗ (Δ[1] : SSet.{u}) ⟶ (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  corePreimageLift ((ihom (Δ[n + 1] : SSet.{u})).map q.hom)
    (r.cylinder.homotopy.h ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj) (by
      rw [Category.assoc, ← (pre (joinStdSimplexIso n 0).inv).naturality q.hom,
        ← Category.assoc]
      exact (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderQuotient_invertsAllEdges r).comp
        ((pre (joinStdSimplexIso n 0).inv).app C.obj))

lemma VerdierFiniteMappingCoconeRecovery.simplexCylinder_ι
    (r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.simplexCylinder r) ≫ (relativeFirstRowSimplex q (n + 1)).ι =
      r.cylinder.homotopy.h ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj := rfl

/-- 元の第一行商を通る同じ円柱は、元の実円柱の商像の座標変換と厳密に一致する。 -/
lemma VerdierFiniteMappingCoconeRecovery.simplexCylinderQuotient_ι
    (r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.simplexCylinder r) ≫ relativeFirstRowSimplexQuotient q (n + 1) ≫
      (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι =
      r.cylinder.homotopy.h ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom ≫
        (pre (joinStdSimplexIso n 0).inv).app C.obj := by
  change (r.cylinder.homotopy.h ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj) ≫
    (ihom (Δ[n + 1] : SSet.{u})).map q.hom = _
  rw [Category.assoc, ← (pre (joinStdSimplexIso n 0).inv).naturality q.hom]

end SerrePositivity.KST.LocalizingInvariants
