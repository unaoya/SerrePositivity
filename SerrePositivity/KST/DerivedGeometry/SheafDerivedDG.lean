module

public import SerrePositivity.KST.DerivedGeometry.LiftedCoefficientComplex
public import SerrePositivity.DifferentialGraded.Quotient.ContractedFunctor
public import SerrePositivity.DifferentialGraded.Category.Homotopy

/-!
# 全係数加群層の複体の acyclic dg 商

概要：実際の層複体の acyclic 条件を用い、既存の Drinfeld dg 商を構成する。
方針：宇宙調整した複体を元の複体へ戻して acyclic を判定する。
規約：この型の構成だけで Mathlib の導来圏との同値を主張しない。
使われ方：KST D4・§13 決定11、Drinfeld dg 商、Toën Derived Azumaya §3.2。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：元の係数加群層の複体が acyclic となる対象の集合。
方針：宇宙調整の圏同値の逆で元の層複体へ戻して判定する。
規約：各項の準連接性は要求しない。
使われ方：KST D4・§13 決定11の dg 商で収縮させる対象。
-/
def acyclicComplexes : Set B.Complexes :=
  fun K => (B.complexLiftEquivalence.inverse.obj K).Acyclic

/--
概要：収縮対象の条件は元の層複体の全コホモロジーが零であること。
方針：各次数で ExactAt と零コホモロジーの同値を使う。
規約：実際の係数加群層のアーベル圏でコホモロジーを取る。
使われ方：KST D4、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の導来模型。
-/
lemma mem_acyclicComplexes_iff (K : B.Complexes) :
    K ∈ B.acyclicComplexes ↔
      ∀ n : ℤ, IsZero ((B.complexLiftEquivalence.inverse.obj K).homology n) := by
  change (∀ n, (B.complexLiftEquivalence.inverse.obj K).ExactAt n) ↔ _
  exact forall_congr' fun n => HomologicalComplex.exactAt_iff_isZero_homology _ n

/--
概要：全係数加群層の複体から acyclic を dg 商した対象型。
方針：既存 Drinfeld 商の対象構成を使う。
規約：小ささは持ち上げた宇宙で自動的に満たし、追加仮定にしない。
使われ方：KST D4・§13 決定11の dg 増強の候補。
-/
abbrev DerivedDG := DGQuotient.QuotientObject B.Complexes B.acyclicComplexes

/--
概要：層複体の acyclic 商に既存の dg 圏構造を与える。
方針：明示的な path dg 商の構造を適用する。
規約：基礎環は宇宙を持ち上げた整数環。
使われ方：KST D4・§13 決定11、Drinfeld dg 商。
-/
instance derivedDGCategory : DGCategory CoefficientDGBase.{u} B.DerivedDG :=
  DGQuotient.quotientDGCategory CoefficientDGBase.{u} B.Complexes B.acyclicComplexes

/--
概要：全層複体の dg 圏から acyclic 商への標準 dg 関手。
方針：空 path の包含から作る既存の商関手を使う。
規約：対象は元の複体と一対一に対応する。
使われ方：KST D4、Toën §3.2 の導来局所化との比較。
-/
def derivedDGProjection : DGFunctor CoefficientDGBase.{u} B.Complexes B.DerivedDG :=
  DGQuotient.inclusion CoefficientDGBase.{u} B.Complexes B.acyclicComplexes

/--
概要：標準 dg 商関手には各 acyclic 対象の指定された収縮が付く。
方針：商の ε 生成元と dε = id の既存証明を使う。
規約：元の acyclic 複体が鎖ホモトピー収縮的であるとは要求しない。
使われ方：KST D4・§13 決定11、Drinfeld dg 商の収縮の普遍性。
-/
def derivedDGContractedProjection :
    DGQuotient.ContractedFunctor CoefficientDGBase.{u} B.Complexes
      B.acyclicComplexes B.DerivedDG :=
  DGQuotient.canonicalContractedFunctor CoefficientDGBase.{u} B.Complexes B.acyclicComplexes

/--
概要：元の層コホモロジーが零の複体は dg 商の H⁰ で零対象になる。
方針：指定収縮の dε = id を境界関係へ渡し、恒等射が零であることを示す。
規約：元の複体自体の鎖収縮性は仮定しない。
使われ方：KST D4・§13 決定11、Drinfeld dg 商と導来局所化の比較への入力。
-/
lemma derivedDG_acyclic_isZero (K : B.Complexes) (hK : K ∈ B.acyclicComplexes) :
    IsZero ((toHomotopy CoefficientDGBase.{u} B.DerivedDG).obj
      (ForgetEnrichment.of (Complex CoefficientDGBase.{u})
        (⟨K⟩ : B.DerivedDG))) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_zero]
  apply (toHomotopy_map_eq_iff_boundary CoefficientDGBase.{u} B.DerivedDG _ _).mpr
  refine ⟨DGQuotient.epsilonElement CoefficientDGBase.{u} B.Complexes B.acyclicComplexes
    ⟨K, hK⟩, ?_⟩
  change (homObject CoefficientDGBase.{u} B.DerivedDG (⟨K⟩ : B.DerivedDG)
      (⟨K⟩ : B.DerivedDG)).d (-1) 0
      (DGQuotient.epsilonElement CoefficientDGBase.{u} B.Complexes B.acyclicComplexes
        ⟨K, hK⟩) =
    (unitElement CoefficientDGBase.{u} (⟨K⟩ : B.DerivedDG)).val - 0
  rw [sub_zero]
  exact DGQuotient.differential_epsilonElement CoefficientDGBase.{u} B.Complexes
    B.acyclicComplexes ⟨K, hK⟩

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
