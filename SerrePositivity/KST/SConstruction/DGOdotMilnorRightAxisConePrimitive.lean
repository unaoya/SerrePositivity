module
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonConeDiagonalAction
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisResolvedLift

/-!
概要：同じ resolved 商上の元右軸比較について、実 cone の第三成分零を固定する。
方針：元 graph の二実 Perf 関手と指定全比較へ一般の零 cochain 証明を特殊化する。
規約：元 cell 始域・同じ resolved 商包含を保持。D2 入力は使わない。
使われ方：実逆回転後の指定合成比較の全自然性を元始域上で証明する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => DGOdotGluing R d
local notation "P" => DGCategoryCellResolution.Source R (B)
local notation "Q" => DGQuotient.QuotientObject (P)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (B)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "F" => dgOdotMilnorRightAxisQuotientSource R d
local notation "G" => dgOdotMilnorRightAxisQuotientTarget R d
local notation "τ" => dgOdotMilnorRightAxisQuotientComparison R d
local notation "T" => DGPerfectComparisonBase R (Q) (F) (G)
local notation "I" => DGFunctor.id (T)
local notation "H" => dgPerfectComparisonHomGluingFunctor R (Q) (F) (G) τ

/-- 概要：同じ元 resolved 右軸比較の実 cone 第三 cochain は全体として零。
方針：同じ二関手・元比較の厳密 gluing 表示へ一般証明を代入する。
規約：射影性・零比較を追加仮定にしない。使われ方：中央射の実 cone 自然性。 -/
lemma dgOdotMilnorRightAxisConePrimitive_zero (x y : P) :
    (Cochain.ofHom ((H).map x y)).comp
      (dgHomGluingConePrimitive R (T) (T) (T) (I) (I) ((H).obj x) ((H).obj y))
      (zero_add (-1)) = 0 :=
  dgPerfectComparisonHomGluingFunctor_conePrimitive_zero R (Q) (F) (G) τ x y
end SerrePositivity.KST.SConstruction
