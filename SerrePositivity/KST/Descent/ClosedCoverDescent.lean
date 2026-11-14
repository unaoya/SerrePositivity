module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Descent.ClosedCoverAction
public import SerrePositivity.KST.Descent.FixedPullbackComparison
public import SerrePositivity.KST.Descent.InvariantProducts

/-!
# 閉和に対する全次数降下の貼り合わせ

## 概要
二つの閉部分と実際の交わり上の指定降下比較から、元の射の全次数降下を導く。

## 方針
構成済みの同変な比較立方体に自然な blowup 列を適用し、有理不変部分の五項補題を使う。

## 規約
自然な列のデータは実降下から供給すべき入力。三つの局所比較は指定された幾何射に対するもの。

## 使われ方
論文 補題 3.3・定理 3.1 の「整 → 被約」の閉和による帰納。
-/

@[expose] public section

universe u w t

open CategoryTheory AlgebraicGeometry Representation

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {B V Y Z : FiniteTypeSchemes S}
variable (f : V ⟶ B) (i : Y ⟶ B) (j : Z ⟶ B)
variable [IsClosedImmersion i.hom.left] [IsClosedImmersion j.hom.left]
variable {G : Type u} [Group G] (action : G →* Aut V)
variable (over_base : ∀ g, (action g).asIso.hom ≫ f = f)

/-- 概要：閉和の交わりへの比較射は基底上の作用に関して不変（論文 補題 3.3）。
方針：構成済みの立方体の左上の同変性と比較先の自明作用を使う。
規約：実際の二重引き戻しから元の交わりへの射。
使われ方：交わり上の PiDescent の指定可換式。 -/
theorem closedCoverIntersection_invariant (g : G) :
    ((closedCoverPullbackSquareAction f i j action over_base).on1 g).asIso.hom ≫
      (closedCoverPullbackCube f i j).τ₁ = (closedCoverPullbackCube f i j).τ₁ :=
  ((closedCoverPullbackCube_equivariant f i j action over_base).equivariant1 g).trans
    (Category.comp_id _)

namespace NaturalBlowupSequences

variable {Coefficient : Type w}
variable {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}

/-- 概要：閉和の同変立方体が定める固定部分の列の比較（論文 補題 3.3）。
方針：始域と基底の実際の二つの抽象 blowup 正方形へ自然な列を適用する。
規約：境界を含む全整数次数の列の射。
使われ方：三つの局所降下から元の射の降下への五項補題。 -/
noncomputable def closedCoverFixedComparison (data : NaturalBlowupSequences L)
    [IsReduced B.obj.left] [IsReduced V.obj.left] [Finite G]
    (covering : Set.range i.hom.left ∪ Set.range j.hom.left = Set.univ) (H : Coefficient) :
    GradedMayerVietoris.Hom
      (data.fixedSequence (closedCoverAbstractBlowup i j covering) H
        (SquareAction.trivial (closedImmersionSquare i j) G))
      (data.fixedSequence (closedCoverPullbackBlowup f i j covering) H
        (closedCoverPullbackSquareAction f i j action over_base)) :=
  data.fixedComparison _ _ _ _ (closedCoverPullbackCube f i j)
    (closedCoverPullbackCube_equivariant f i j action over_base) H

/-- 概要：二つの閉部分と交わり上の全次数降下を貼り合わせる（論文 補題 3.3）。
方針：積の不変部分の比較と交わりの比較から五項補題を適用し、元の指定比較へ戻す。
規約：元の射の降下を仮定せず、三つの実際の小さい基底上の降下を入力する。
使われ方：閉和から被約な基底の既約成分への帰納。 -/
theorem closedCover_piDescent (data : NaturalBlowupSequences L)
    [IsReduced B.obj.left] [IsReduced V.obj.left] [Finite G]
    (covering : Set.range i.hom.left ∪ Set.range j.hom.left = Set.univ)
    (left_descent : L.PiDescent (closedImmersionSquare f i).f₁₃
      (closedBaseChangeAction f i action over_base)
      (closedBaseChangeAction_over_base f i action over_base))
    (right_descent : L.PiDescent (closedImmersionSquare f j).f₁₃
      (closedBaseChangeAction f j action over_base)
      (closedBaseChangeAction_over_base f j action over_base))
    (intersection_descent : L.PiDescent (closedCoverPullbackCube f i j).τ₁
      (closedCoverPullbackSquareAction f i j action over_base).on1
      (closedCoverIntersection_invariant f i j action over_base)) :
    L.PiDescent f action over_base := by
  intro H n
  let comparison := data.closedCoverFixedComparison f i j action over_base covering H
  have product_bijective (k : ℤ) : Function.Bijective (comparison.mapB k) := by
    exact invariantMap_product_bijective _ _
      (L.fixedPullbackIntertwining_bijective H k _ _ _ (left_descent H k))
      (L.fixedPullbackIntertwining_bijective H k _ _ _ (right_descent H k))
  have intersection_bijective (k : ℤ) : Function.Bijective (comparison.mapC k) :=
    L.fixedPullbackIntertwining_bijective H k _ _ _ (intersection_descent H k)
  have base_bijective := comparison.bijective_mapA product_bijective intersection_bijective n
  let source := trivialInvariantsEquiv (L.pullbackRepresentation H n (1 : G →* Aut B))
  let target := L.invariantSubmoduleEquiv H n action
  have agrees : (fun x ↦ target.symm (comparison.mapA n (source.symm x))) =
      L.invariantComparison H n f action over_base := by
    funext x
    apply Subtype.ext
    rfl
  rw [← agrees]
  exact target.symm.bijective.comp (base_bijective.comp source.symm.bijective)

end NaturalBlowupSequences

end SerrePositivity.KST.Descent

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Proof step A.2 Step 1" (partial := component) "仮定：有限型スキーム、被約な始域と基底、有限群作用、次数付き前層のブローアップ完全列、各制限での降下を仮定（Lean が強い）。結論：閉被覆と交わりでの同変降下から、基底全体での次数別降下を得る。切断型不変量からの Sp 引き戻しの構成は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.Descent.NaturalBlowupSequences.closedCover_piDescent
