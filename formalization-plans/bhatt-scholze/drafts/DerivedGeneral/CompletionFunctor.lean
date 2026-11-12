-- 将来の置き場所：InfinityCategories の Derived の上（調整役が判断。M12 と同じ扱い）。BS 固有ではない一般論。
-- 設計書：formalization-plans/bhatt-scholze/a2-design.md G-A2-3。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.BaseChange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Homology
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.StableLimits
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Reflective
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion

/-!
# 導来 (p,d) 完備化の ∞ 関手

## 概要
D(A) の導来 (p,d) 完備な対象のなす充満部分 ∞ 圏 D(A)_comp と、包含の左随伴（反射）としての完備化 X ↦ X^∧。
完備な対象の特徴づけ（Koszul 塔の極限、`IsModuleComplete` の D(A) 版）、完備化が完全であること、余極限の完備化、
完備化単位が有限の冪 Koszul 複体とのテンソルを変えないこと。

## 方針
複体の側の既存の導来完備化（HA/DerivedCompletion の `koszulCompletionObject`、`PDCompletionH0` など）を dg nerve で ∞ 関手にし、
反射であることを `IsReflectiveSubcategory`（F1B/Localization/Reflective）の形で述べる。

## 規約
有限集合 s の元ごとの導来完備性を使う。prism の (p,d) は適用側の特殊化。

## 使われ方
A2-2（Kan 延長の値を (p,d) 完備化する）、A2-4（底変換・テンソルの完備化）、A4（Def 8.2 の Frobenius 余極限の完備化）、
Lemma 4.22（Tot と完備底変換）。2b の後に HA/DerivedCompletion の名前に合わせる。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.InfinityCategories.Derived

open MonoidalCategory SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

/-- 一元 a での導来完備性を D(A) の頂点に引き戻す。 -/
def completeAt {A : Type u} [CommRing A] (a : A) (x : (derivedInfinityCategory A) _⦋0⦌) : Prop :=
  IsComplete A a ((derivedInfinityHomotopyEquivalence A).functor.obj ⟨x⟩)

variable (A : Type u) [CommRing A]

/-- s の各元について完備。空集合では全ての頂点を含む。 -/
def IsDerivedComplete (s : Finset A) (x : (derivedInfinityCategory A) _⦋0⦌) : Prop :=
  ∀ a ∈ s, completeAt a x

abbrev completeSubcomplex (s : Finset A) : (derivedInfinityCategory A).Subcomplex :=
  fullSubcomplexOnVertices _ (IsDerivedComplete A s)

/-- Koszul 塔の極限から作る反射。随伴の単位が X → X^∧ を指定する。 -/
def completionReflection (s : Finset A) :
    Σ L : derivedInfinityCategory A ⟶ (completeSubcomplex A s : SSet),
      QCatAdjunction L (completeSubcomplex A s).ι := by
  sorry -- M13：Koszul 塔による導来完備化の普遍性を dg nerve に移す

theorem completion_isReflective (s : Finset A) :
    IsReflectiveSubcategory (derivedInfinityCategory A) (IsDerivedComplete A s) :=
  ⟨⟨(completionReflection A s).1, (completionReflection A s).2⟩⟩

def completion (s : Finset A) : derivedInfinityCategory A ⟶ derivedInfinityCategory A :=
  (completionReflection A s).1 ≫ (completeSubcomplex A s).ι

def completionUnit (s : Finset A) : FunctorHom (𝟙 _) (completion A s) :=
  (completionReflection A s).2.unitHom

/-- 台の D(A) の頂点が完備な E∞ 代数。 -/
abbrev cAlgCompleteSubcomplex (s : Finset A) : (E.CAlg A).Subcomplex :=
  fullSubcomplexOnVertices _ (fun x => IsDerivedComplete A s ((E.forget A).app _ x))

def cAlgCompletionReflection (s : Finset A) :
    Σ L : E.CAlg A ⟶ (cAlgCompleteSubcomplex (E := E) A s : SSet),
      QCatAdjunction L (cAlgCompleteSubcomplex (E := E) A s).ι := by
  sorry -- M13-CAlg：加群の完備反射を対称モノイダル局所化として代数へ移す

def cAlgCompletion (s : Finset A) : E.CAlg A ⟶ E.CAlg A :=
  (cAlgCompletionReflection (E := E) A s).1 ≫ (cAlgCompleteSubcomplex (E := E) A s).ι

def cAlgCompletionUnit (s : Finset A) : FunctorHom (𝟙 _) (cAlgCompletion (E := E) A s) :=
  (cAlgCompletionReflection (E := E) A s).2.unitHom

/-- s を列 a として並べる。完備化単位を表す任意の辺に Kos(a₁^n,…,aᵣ^n;−) を
適用した鎖写像は各次数のホモロジーに同型を誘導する。 -/
theorem completion_tensor_koszul (s : Finset A) {r : ℕ} (a : Fin r → A)
    (ha : Set.range a = (s : Set A)) (n : ℕ) (x : (derivedInfinityCategory A) _⦋0⦌)
    (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (derivedInfinityCategory A))
      x ((completion A s).app _ x))
    (he : SSet.Truncated.HomotopyCategory.homMk e = functorHomEvaluate (completionUnit A s) x)
    (i : ℤ) :
    IsIso (HomologicalComplex.homologyMap ((koszulFunctor (fun j => a j ^ n)).map
      (DGNerve.edgeChainMap (e.map ((SSet.truncation 2).map derivedInfinityInclusion)))) i) := by
  sorry -- Koszul 完備化単位は各有限 Koszul 商を変えない。koszulFunctor の対象部分は koszulComplexOn

/-- 完備化は pullback 四角形を保つので fiber 列を保つ。 -/
theorem completion_exact (s : Finset A)
    (Q : (Δ[1] ⊗ Δ[1] : SSet.{u+1}) ⟶ derivedInfinityCategory A) (hQ : IsPullbackSquare Q) :
    IsPullbackSquare (Q ≫ completion A s) := by
  sorry -- Koszul 塔での有限極限と塔の極限の交換

/-- 完備部分圏への反射で余極限錐を写す。 -/
theorem complete_colimit (s : Finset A) {K : SSet.{u+1}} {F : K ⟶ derivedInfinityCategory A}
    (c : JoinCocone F) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (completionReflection A s).1 c) := by
  sorry -- completionReflection の左随伴は余極限を保つ

/-- D 加群の完備底変換。環準同型と有限集合を入力し、標的では元の像に沿って完備化する。 -/
def completedBaseChange {A : Type u} [CommRing A] {B : Type u} [CommRing B] (f : A →+* B) (s : Finset A) :
    derivedInfinityCategory A ⟶ derivedInfinityCategory B := by
  classical
  exact derivedInfinityBaseChange f ≫ completion B (s.image f)

end SerrePositivity.InfinityCategories.Derived
