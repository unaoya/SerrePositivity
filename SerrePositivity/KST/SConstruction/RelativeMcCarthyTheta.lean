module
public import SerrePositivity.KST.SConstruction.RelativeThetaMembership

/-! # 相対左 fiber 内の第二の θ ホモトピー
概要：ρ の相対終端から quotient と切断の合成への実単体ホモトピーを構成する。
方針：全時刻の B 所属で θ を持ち上げ、単射な忘却で両端を反映する。
規約：周囲の二つのホモトピーを同じ相対左 fiber に制限する。使われ方：相対 quotient の弱同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 積の端点の包含は第一因子の射と厳密に可換。 -/
lemma tensorIntervalEndpoint_naturality {K L : SSet.{u}} (f : K ⟶ L) (i : Fin 2) :
    lift (𝟙 K) (SSet.const (stdSimplex.obj₀Equiv.symm i)) ≫ (f ▷ (Δ[1] : SSet.{u})) =
      f ≫ lift (𝟙 L) (SSet.const (stdSimplex.obj₀Equiv.symm i)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 相対 ρ の終端は忘却によって周囲の ρ の終端を回収する。 -/
lemma relativeMcCarthyRhoTerminal_forget {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeMcCarthyRhoTerminal A B a ≫ relativeCofiberLeftFiberForget A B a =
      relativeCofiberLeftFiberForget A B a ≫
        mcCarthyRhoTerminal X (relativeCofiberBaseSimplex A a) := by
  rw [relativeMcCarthyRhoTerminal, Category.assoc, relativeMcCarthyRhoFiberMap_forget,
    ← Category.assoc, tensorIntervalEndpoint_naturality, Category.assoc]
  rfl

/-- 同じ相対左 fiber 内へ持ち上げた元の θ の実単体的な族。 -/
def relativeMcCarthyThetaFiberMap {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeCofiberSubobjectLeftFiber A B a ⊗ Δ[1] ⟶ relativeCofiberSubobjectLeftFiber A B a :=
  relativeCofiberLeftFiberLift A B a
    ((relativeCofiberLeftFiberForget A B a ▷ (Δ[1] : SSet.{u})) ≫
      mcCarthyThetaFiberMap X (relativeCofiberBaseSimplex A a))
    (relativeMcCarthyTheta_quotient_in_closed A B a)

/-- 相対 θ は忘却によって元の周囲の θ の前合成を厳密に回収する。 -/
lemma relativeMcCarthyThetaFiberMap_forget {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeMcCarthyThetaFiberMap A B a ≫ relativeCofiberLeftFiberForget A B a =
      (relativeCofiberLeftFiberForget A B a ▷ (Δ[1] : SSet.{u})) ≫
        mcCarthyThetaFiberMap X (relativeCofiberBaseSimplex A a) :=
  relativeCofiberLeftFiberLift_forget _ _ _ _ _

/-- 相対 θ の零時刻は相対 ρ の終端。 -/
lemma relativeMcCarthyThetaFiberMap_zero {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    lift (𝟙 (relativeCofiberSubobjectLeftFiber A B a))
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ relativeMcCarthyThetaFiberMap A B a =
      relativeMcCarthyRhoTerminal A B a := by
  apply (cancel_mono (relativeCofiberLeftFiberForget A B a)).1
  rw [Category.assoc, relativeMcCarthyThetaFiberMap_forget, ← Category.assoc,
    tensorIntervalEndpoint_naturality, Category.assoc, mcCarthyThetaFiberMap_zero,
    relativeMcCarthyRhoTerminal_forget]

/-- 相対 θ の一時刻は相対 quotient と切断の合成。 -/
lemma relativeMcCarthyThetaFiberMap_one {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    lift (𝟙 (relativeCofiberSubobjectLeftFiber A B a))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ relativeMcCarthyThetaFiberMap A B a =
      relativeCofiberLeftFiberQuotient A B a ≫ relativeMcCarthyFiberSection A B a := by
  apply (cancel_mono (relativeCofiberLeftFiberForget A B a)).1
  rw [Category.assoc, relativeMcCarthyThetaFiberMap_forget, ← Category.assoc,
    tensorIntervalEndpoint_naturality, Category.assoc, mcCarthyThetaFiberMap_one,
    Category.assoc, relativeMcCarthyFiberSection_forget, ← Category.assoc,
    relativeCofiberLeftFiberForget_quotient, Category.assoc]

/-- 相対 ρ の終端から相対 quotient と切断の合成への実単体ホモトピー。 -/
def relativeMcCarthyThetaHomotopy {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    SSet.Homotopy (relativeMcCarthyRhoTerminal A B a)
      (relativeCofiberLeftFiberQuotient A B a ≫ relativeMcCarthyFiberSection A B a) where
  h := relativeMcCarthyThetaFiberMap A B a
  h₀ := relativeMcCarthyThetaFiberMap_zero A B a
  h₁ := relativeMcCarthyThetaFiberMap_one A B a
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    exact False.elim v.1.property

end SerrePositivity.KST.SConstruction
