module
public import SerrePositivity.KST.SConstruction.SpanPrisms

/-! # McCarthy の押し出し span の coherent な族
概要：同じ subobject 上の λ→μ と λ→ν を span の族に貼り合わせる。
方針：左 fiber の等号が二枝の共通始点を厳密に一致させる。
規約：上辺は 01、左辺は 02。使われ方：点ごとの正規化した押し出しによる ρ。
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

/-- 概要：左 fiber の一致条件で McCarthy の二枝を span に貼る。
方針：subobject の等号で共通始点を照合して pushout の普遍性を使う。
規約：元の cofiber 図式 E と動かす添字を全て保持する。使われ方：ρ の実際の入力。 -/
def mcCarthySpan {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) : (horn 2 0 : SSet.{u}) ⊗ arNerve n ⟶ cofiberDiagrams C :=
  spanPrisms (mcCarthyLambdaMu z A α τ) (mcCarthyLambdaNu z E) (by
    rw [mcCarthyLambdaMu_zero, mcCarthyLambdaNu_zero]
    have he := congrArg (fun f : arNerve n ⟶ C => f ≫ zeroCofiberFunctor z false) h
    simpa only [mcCarthyLambda, Category.assoc] using he.symm)

/-- 概要：McCarthy の span の上辺は λ→μ の指定した prism。
方針：二枝の貼り合わせの第一制限。
規約：全高次単体での等号。使われ方：ρ の上辺の照合。 -/
lemma mcCarthySpan_upper {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) :
    (horn₂₀.ι₀₁ ▷ arNerve n) ≫ mcCarthySpan z A α τ E h = mcCarthyLambdaMu z A α τ :=
  spanPrisms_left _ _ _

/-- 概要：McCarthy の span の左辺は λ→ν の指定した prism。
方針：二枝の貼り合わせの第二制限。
規約：全高次単体での等号。使われ方：ρ の左辺の照合。 -/
lemma mcCarthySpan_left {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) :
    (horn₂₀.ι₀₂ ▷ arNerve n) ≫ mcCarthySpan z A α τ E h = mcCarthyLambdaNu z E :=
  spanPrisms_right _ _ _

/-- 概要：McCarthy の span は全ての Ar の添字制限と可換。
方針：二枝で prism の前合成の式を確認する。
規約：左 fiber の等号の証明の選択によらない。使われ方：ρ の面・退化の自然性。 -/
lemma mcCarthySpan_pre {l n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) (σ : Fin (l + 1) →o Fin (n + 1))
    (h' : (arNerveMap σ ≫ E) ≫ cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = arNerveMap (α.comp σ) ≫ A) :
    ((horn 2 0 : SSet.{u}) ◁ arNerveMap σ) ≫ mcCarthySpan z A α τ E h =
      mcCarthySpan z A (α.comp σ) (τ.comp σ) (arNerveMap σ ≫ E) h' := by
  apply spanPrisms_hom_ext
  · rw [← Category.assoc, ← whisker_exchange, Category.assoc, mcCarthySpan_upper,
      mcCarthySpan_upper, mcCarthyLambdaMu_pre]
  · rw [← Category.assoc, ← whisker_exchange, Category.assoc, mcCarthySpan_left,
      mcCarthySpan_left, mcCarthyLambdaNu_pre]

/-- 概要：上辺の prism の subobject は Ar の添字の変換そのもの。
方針：標準恒等 cofiber の入力の始点が恒等関手である式を使う。
規約：射の厳密な等号。使われ方：ρ の subobject を μ に一致させる正規化。 -/
lemma mcCarthyLambdaMu_source {n m : ℕ} {C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) :
    mcCarthyLambdaMu z A α τ ≫ cofiberProjection C ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = mcCarthyArMotion α τ ≫ A := by
  simp only [mcCarthyLambdaMu, Category.assoc]
  rw [zeroCofiberFunctor_input_evaluation]
  simp

/-- 概要：時刻の単体が全て零なら McCarthy の span は左辺だけからなる恒等 span。
方針：λ→μ は一定であり、左 fiber 条件で左辺の始点が λ となる。
規約：標準形状の厳密な等号。使われ方：ρ の恒等射側の端点。 -/
lemma mcCarthySpan_timeZero {n m : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (A : arNerve m ⟶ C) (α : Fin (n + 1) →o Fin (m + 1))
    (E : arNerve n ⟶ cofiberDiagrams C)
    (h : E ≫ cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      arNerveMap α ≫ A) :
    mcCarthySpan z A α (OrderHom.const _ 0) E h =
      (identitySpanShape false ▷ arNerve n) ≫ mcCarthyLambdaNu z E := by
  apply spanPrisms_constant_left _ _ _ (mcCarthyLambda z A α)
  · exact mcCarthyLambdaMu_timeZero z A α
  · rw [mcCarthyLambdaNu_zero]
    have he := congrArg (fun f : arNerve n ⟶ C => f ≫ zeroCofiberFunctor z false) h
    simpa only [mcCarthyLambda, Category.assoc] using he

end SerrePositivity.KST.SConstruction
