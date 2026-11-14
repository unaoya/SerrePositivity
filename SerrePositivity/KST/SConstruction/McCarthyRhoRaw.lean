module
public import SerrePositivity.KST.SConstruction.McCarthySpan
public import SerrePositivity.KST.SConstruction.PointwisePushoutApex

/-! # McCarthy の ρ の元の正方形の族
概要：λ・μ・ν の span を C 内で点ごとに押し出して、ρ の元の図式を構成する。
方針：cofiber 図式の包含後に座標を交換し、同じ正規化した押し出し選択を使う。
規約：cofiber 性・gapped 性・fiber 条件の証明は別項目。使われ方：McCarthy の実ホモトピーの候補。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：McCarthy の span から C 内の点ごとの押し出しで ρ の正方形の族を構成する。
方針：正方形と span の座標を交換し、押し出し頂点の族を元に戻す。
規約：値はまだ cofiber の全部分複体に持ち上げない。使われ方：実ホモトピーの構成。 -/
def mcCarthyRhoRaw {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) : arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C :=
  pointwiseDiagramPushoutApex
    (mcCarthySpan z A α τ E h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι)

/-- 概要：元の ρ の族は全ての面・退化による Ar の前合成と可換。
方針：span の自然性と C 内の点ごとの同じ押し出し選択の自然性。
規約：単体の図式全体の厳密な等号。使われ方：ρ を単体ホモトピーに束ねる。 -/
lemma mcCarthyRhoRaw_pre {l n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) (σ : Fin (l + 1) →o Fin (n + 1))
    (h' : (arNerveMap σ ≫ E) ≫ cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = arNerveMap (α.comp σ) ≫ A) :
    mcCarthyRhoRaw z A (α.comp σ) (τ.comp σ) (arNerveMap σ ≫ E) h' =
      arNerveMap σ ≫ mcCarthyRhoRaw z A α τ E h := by
  rw [mcCarthyRhoRaw, ← mcCarthySpan_pre z A α τ E h σ h', Category.assoc,
    pointwiseDiagramPushoutApex_pre]
  rfl

/-- 概要：時刻の単体が全て零なら元の ρ の族は元の cofiber 図式そのもの。
方針：恒等な上辺の span と C 内の点ごとの押し出しの正規化を使う。
規約：正方形の族全体を厳密に回収する。使われ方：ρ のホモトピーの恒等射側の端点。 -/
lemma mcCarthyRhoRaw_timeZero {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) :
    mcCarthyRhoRaw z A α (OrderHom.const _ 0) E h =
      E ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι := by
  rw [mcCarthyRhoRaw, mcCarthySpan_timeZero, Category.assoc,
    pointwiseDiagramPushoutApex_identity, ← Category.assoc, mcCarthyLambdaNu_one]

end SerrePositivity.KST.SConstruction
