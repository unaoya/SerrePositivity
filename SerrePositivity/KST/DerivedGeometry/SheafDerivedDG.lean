module

public import SerrePositivity.KST.DerivedGeometry.LiftedCoefficientComplex
public import SerrePositivity.KST.DerivedGeometry.DGResolution.VerdierTransport
public import SerrePositivity.DifferentialGraded.Quotient.Path.Evaluation
public import SerrePositivity.DifferentialGraded.Category.Basic

/-!
# 全係数加群層の複体の acyclic dg 商

概要：実際の層複体の dg 圏を平坦分解してから acyclic の dg 商を構成する。
方針：一般の生成元添加による分解と acyclic 条件の逆像に既存 path 商を適用する。
規約：Hom の K-flat 性は一般分解のフィルトレーションで証明済み。
Mathlib の導来圏との H⁰ 同値は未証明。
使われ方：KST D4・§13 決定11、Drinfeld Thm 3.4・§3.5、Toën Derived Azumaya §3.2。
採用された平坦分解の構成はレーン計画 §26–28 に記録する。
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
概要：全係数加群層の複体の一般的な平坦分解の対象型。
方針：閉元被覆と境界生成元添加の具体的な余極限を使う。
規約：小ささは持ち上げた宇宙で満たす。
使われ方：Drinfeld Lemma 13.5、KST D4・§13 決定11。
-/
abbrev ResolvedComplexes := DGResolution.Objects CoefficientDGBase.{u} B.Complexes

/--
概要：平坦分解から元の層複体の dg 圏への増大準同値。
方針：一般の具体的分解を層複体へ適用する。
規約：元の層の Hom の平坦性は要求しない。
使われ方：Drinfeld Lemma 13.5・§3.5、KST D4 の導来商の屋根。
-/
def resolvedAugmentation : DGFunctor CoefficientDGBase.{u} B.ResolvedComplexes B.Complexes :=
  DGResolution.augmentation CoefficientDGBase.{u} B.Complexes

/--
概要：平坦分解の増大関手は準同値。
方針：一般分解の境界充填の証明を使う。
規約：層の特殊な平坦性仮定は加えない。
使われ方：Drinfeld Lemma 13.5、KST D4 の導来比較。
-/
theorem resolvedAugmentation_quasiEquivalence : QuasiEquivalence B.resolvedAugmentation :=
  DGResolution.augmentation_quasiEquivalence CoefficientDGBase.{u} B.Complexes

/--
概要：平坦分解の中で、像の層複体が acyclic となる対象集合。
方針：実際の層コホモロジーによる既存条件の逆像を取る。
規約：準連接性はここでは要求しない。
使われ方：Drinfeld §3.5、KST D4 の収縮対象。
-/
def resolvedAcyclicComplexes : Set B.ResolvedComplexes :=
  DGResolution.nullObjects CoefficientDGBase.{u} B.Complexes B.acyclicComplexes

/--
概要：全係数加群層の複体を平坦分解してから acyclic を商した対象型。
方針：一般の分解後の path 商を使う。
規約：未分解の全層複体の path 商は使わない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4・§13 決定11。
-/
abbrev DerivedDG := DGResolution.Quotient CoefficientDGBase.{u} B.Complexes B.acyclicComplexes

/--
概要：層複体の acyclic 商に既存の dg 圏構造を与える。
方針：分解後の Hom 複体に明示的 path dg 商の構造を適用する。
規約：基礎環は宇宙を持ち上げた整数環。
使われ方：KST D4・§13 決定11、Drinfeld Thm 3.4・§3.5。
-/
instance derivedDGCategory : DGCategory CoefficientDGBase.{u} B.DerivedDG :=
  DGQuotient.quotientDGCategory CoefficientDGBase.{u} B.ResolvedComplexes B.resolvedAcyclicComplexes

/--
概要：全層複体の平坦分解から acyclic 商への標準 dg 関手。
方針：空 path の包含から作る既存の商関手を使う。
規約：対象は元の複体と一対一に対応する。
使われ方：KST D4、Toën §3.2 の導来局所化との比較。
-/
def derivedDGProjection : DGFunctor CoefficientDGBase.{u} B.ResolvedComplexes B.DerivedDG :=
  DGResolution.projection CoefficientDGBase.{u} B.Complexes B.acyclicComplexes

/--
概要：標準 dg 商関手には各 acyclic 対象の指定された収縮が付く。
方針：商の ε 生成元と dε = id の既存証明を使う。
規約：元の acyclic 複体が鎖ホモトピー収縮的であるとは要求しない。
使われ方：KST D4・§13 決定11、Drinfeld dg 商の収縮の普遍性。
-/
def derivedDGContractedProjection :
    DGQuotient.ContractedFunctor CoefficientDGBase.{u} B.ResolvedComplexes
      B.resolvedAcyclicComplexes B.DerivedDG :=
  DGQuotient.canonicalContractedFunctor CoefficientDGBase.{u} B.ResolvedComplexes
    B.resolvedAcyclicComplexes

/--
概要：元の層コホモロジーが零の複体は dg 商の H⁰ で零対象になる。
方針：指定収縮の dε = id を境界関係へ渡し、恒等射が零であることを示す。
規約：元の複体自体の鎖収縮性は仮定しない。
使われ方：KST D4・§13 決定11、Drinfeld dg 商と導来局所化の比較への入力。
-/
lemma derivedDG_acyclic_isZero (K : B.ResolvedComplexes) (hK : K ∈ B.resolvedAcyclicComplexes) :
    IsZero ((toHomotopy CoefficientDGBase.{u} B.DerivedDG).obj
      (ForgetEnrichment.of (Complex CoefficientDGBase.{u})
        (⟨K⟩ : B.DerivedDG))) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_zero]
  apply (toHomotopy_map_eq_iff_boundary CoefficientDGBase.{u} B.DerivedDG _ _).mpr
  refine ⟨DGQuotient.epsilonElement CoefficientDGBase.{u} B.ResolvedComplexes B.resolvedAcyclicComplexes
    ⟨K, hK⟩, ?_⟩
  change (homObject CoefficientDGBase.{u} B.DerivedDG (⟨K⟩ : B.DerivedDG)
      (⟨K⟩ : B.DerivedDG)).d (-1) 0
      (DGQuotient.epsilonElement CoefficientDGBase.{u} B.ResolvedComplexes B.resolvedAcyclicComplexes
        ⟨K, hK⟩) =
    (unitElement CoefficientDGBase.{u} (⟨K⟩ : B.DerivedDG)).val - 0
  rw [sub_zero]
  exact DGQuotient.differential_epsilonElement CoefficientDGBase.{u} B.ResolvedComplexes
    B.resolvedAcyclicComplexes ⟨K, hK⟩

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
