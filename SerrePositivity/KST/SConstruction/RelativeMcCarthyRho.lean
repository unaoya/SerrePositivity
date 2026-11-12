module
public import SerrePositivity.KST.SConstruction.RelativeFiberForgetMono

/-! # 相対左 fiber 内の McCarthy の ρ
概要：quotient を厳密に固定する周囲の ρ は相対左 fiber に持ち上がる。
方針：基底 A の条件と quotient の B 所属で全成分条件を回収する。
規約：元のパラメーターと正方形を保持する。使われ方：相対左 fiber の第一ホモトピー。
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

/-- 周囲の ρ を相対左 fiber から前合成した族は全時刻で quotient が B に入る。 -/
lemma relativeMcCarthyRho_quotient_in_closed {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌)
    (n : SimplexCategoryᵒᵖ) (x : (relativeCofiberSubobjectLeftFiber A B a ⊗ Δ[1]).obj n) :
    ObjectSInClosed B
      (((relativeCofiberLeftFiberForget A B a ▷ (Δ[1] : SSet.{u})) ≫
        mcCarthyRhoFiberMap X (relativeCofiberBaseSimplex A a) ≫
          cofiberLeftFiberQuotient X (relativeCofiberBaseSimplex A a)).app n x) := by
  rw [mcCarthyRhoFiberMap_quotient]
  rcases n with ⟨⟨n⟩⟩
  exact relativeCofiberLeftFiberForget_quotient_in_closed A B a x.1

/-- 同じ C 内の選択を保持する相対左 fiber の ρ の実単体的な族。 -/
def relativeMcCarthyRhoFiberMap {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeCofiberSubobjectLeftFiber A B a ⊗ Δ[1] ⟶ relativeCofiberSubobjectLeftFiber A B a :=
  relativeCofiberLeftFiberLift A B a
    ((relativeCofiberLeftFiberForget A B a ▷ (Δ[1] : SSet.{u})) ≫
      mcCarthyRhoFiberMap X (relativeCofiberBaseSimplex A a))
    (relativeMcCarthyRho_quotient_in_closed A B a)

/-- 相対 ρ は周囲へ忘れると元の McCarthy の ρ の前合成を回収する。 -/
lemma relativeMcCarthyRhoFiberMap_forget {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeMcCarthyRhoFiberMap A B a ≫ relativeCofiberLeftFiberForget A B a =
      (relativeCofiberLeftFiberForget A B a ▷ (Δ[1] : SSet.{u})) ≫
        mcCarthyRhoFiberMap X (relativeCofiberBaseSimplex A a) :=
  relativeCofiberLeftFiberLift_forget _ _ _ _ _

/-- 相対 ρ の零時刻は同じ相対左 fiber の恒等射。 -/
lemma relativeMcCarthyRhoFiberMap_zero {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    lift (𝟙 (relativeCofiberSubobjectLeftFiber A B a))
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ relativeMcCarthyRhoFiberMap A B a =
      𝟙 _ := by
  apply (cancel_mono (relativeCofiberLeftFiberForget A B a)).1
  rw [Category.assoc, relativeMcCarthyRhoFiberMap_forget, ← Category.assoc]
  have he : lift (𝟙 (relativeCofiberSubobjectLeftFiber A B a))
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      (relativeCofiberLeftFiberForget A B a ▷ (Δ[1] : SSet.{u})) =
    relativeCofiberLeftFiberForget A B a ≫
      lift (𝟙 (cofiberSubobjectLeftFiber X (relativeCofiberBaseSimplex A a)))
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro e
    rfl
  rw [he, Category.assoc, mcCarthyRhoFiberMap_zero, Category.comp_id, Category.id_comp]

/-- 相対 ρ は B の元の quotient への射を全時刻で厳密に固定する。 -/
lemma relativeMcCarthyRhoFiberMap_quotient {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeMcCarthyRhoFiberMap A B a ≫ relativeCofiberLeftFiberQuotient A B a =
      fst (relativeCofiberSubobjectLeftFiber A B a) (Δ[1] : SSet.{u}) ≫
        relativeCofiberLeftFiberQuotient A B a := by
  have : Mono (closedStableInclusion B).val :=
    inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.carrier B.predicate).ι)
  apply (cancel_mono (objectSConstructionFunctor.map (closedStableInclusion B))).1
  rw [Category.assoc, ← relativeCofiberLeftFiberForget_quotient, ← Category.assoc,
    relativeMcCarthyRhoFiberMap_forget, Category.assoc, mcCarthyRhoFiberMap_quotient,
    ← Category.assoc, whiskerRight_fst, Category.assoc,
    relativeCofiberLeftFiberForget_quotient, ← Category.assoc]

/-- 相対 ρ の終端を同じ相対左 fiber 内で定義する。 -/
def relativeMcCarthyRhoTerminal {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeCofiberSubobjectLeftFiber A B a ⟶ relativeCofiberSubobjectLeftFiber A B a :=
  lift (𝟙 (relativeCofiberSubobjectLeftFiber A B a))
    (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ relativeMcCarthyRhoFiberMap A B a

/-- 相対左 fiber の恒等射から ρ の終端への実際の単体ホモトピー。 -/
def relativeMcCarthyRhoHomotopy {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    SSet.Homotopy (𝟙 (relativeCofiberSubobjectLeftFiber A B a))
      (relativeMcCarthyRhoTerminal A B a) where
  h := relativeMcCarthyRhoFiberMap A B a
  h₀ := relativeMcCarthyRhoFiberMap_zero A B a
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    exact False.elim v.1.property

end SerrePositivity.KST.SConstruction
