module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RelativeConstFiberEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.UniversalScaffoldEvaluation

/-!
概要：全相対関手の実端点評価は、元の相対前合成と同じ定値 fiber 評価の合成。
方針：uncurry して fiber 包含後を比較し、元の相対評価と結合子の実端点を計算する。
規約：相対比較の指定値を変えない。使われ方：全三角形の最後面と元の終点像の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全相対関手の同じ実端点評価を、元の相対前合成・底の等式・fiber 評価で厳密に読む。 -/
lemma relativePrismEvaluationEndpoint_curry_eq_pre {E B A : SSet.{u}}
    (p : E ⟶ B) (β : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (i : Fin 2) (z : B _⦋0⦌) (h : prismEndpoint i A ≫ β = SSet.const z) :
    curry (relativePrismEvaluationEndpoint p β i z h) =
      relativeFunctorPre p β (prismEndpoint i A) ≫
        eqToHom (congrArg (relativeFunctorSpace p) h) ≫ relativeFunctorConstFiberHom p z := by
  apply uncurry_injective
  apply (cancel_mono (vertexFiberι p z)).mp
  rw [uncurry_curry, ← relativePrismEvaluationEndpoint_ι p β i z h]
  change prismEndpoint i (A ⊗ relativeFunctorSpace p β) ≫ relativePrismEvaluationPrism p β =
    uncurry ((relativeFunctorPre p β (prismEndpoint i A) ≫
      (eqToIso (congrArg (relativeFunctorSpace p) h)).hom) ≫
        (relativeFunctorConstFiberIso p z).hom) ≫ vertexFiberι p z
  rw [relativeConstFiberIso_uncurry p z, relativeFunctorUncurry_transport p h]
  have hu := relativeFunctorUncurry_pre (p := p) (𝟙 (relativeFunctorSpace p β))
    (prismEndpoint i A)
  rw [Category.id_comp] at hu
  rw [hu, relativePrismEvaluationPrism, ← Category.assoc]
  have he : prismEndpoint i (A ⊗ relativeFunctorSpace p β) ≫
      (α_ (Δ[1] : SSet.{u}) A (relativeFunctorSpace p β)).inv =
      prismEndpoint i A ▷ relativeFunctorSpace p β := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [he]

/-- 元の全図式の辺への制限後の実端点評価は、同じ合成した部分図式での評価。 -/
lemma relativePrismEvaluationEndpoint_restrict_eq_pre {D E B A : SSet.{u}}
    (p : E ⟶ B) (β : D ⟶ B) (r : (Δ[1] : SSet.{u}) ⊗ A ⟶ D)
    (i : Fin 2) (z : B _⦋0⦌) (h : (prismEndpoint i A ≫ r) ≫ β = SSet.const z) :
    relativeFunctorPre p β r ≫
      curry (relativePrismEvaluationEndpoint p (r ≫ β) i z
        ((Category.assoc (prismEndpoint i A) r β).symm.trans h)) =
    relativeFunctorPre p β (prismEndpoint i A ≫ r) ≫
      eqToHom (congrArg (relativeFunctorSpace p) h) ≫ relativeFunctorConstFiberHom p z := by
  rw [relativePrismEvaluationEndpoint_curry_eq_pre p (r ≫ β) i z
    ((Category.assoc (prismEndpoint i A) r β).symm.trans h), ← Category.assoc,
    relativeFunctorPre_comp]

end SerrePositivity.InfinityCategories.F2
