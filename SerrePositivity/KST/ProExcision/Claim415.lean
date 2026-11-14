module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.ProExcision.Claim415Relative
public import SerrePositivity.KST.ProExcision.RightColumnBlockComponents

/-!
# Claim 4.15 の有限 rank の相対零化

概要：基底のブロック和と列の右乗法の零埋めが誘導する相対写像を低次で零化する。
方針：実三角群を経由する合成を構成し、その二成分を通常の写像と同定する。
規約：KST Claim 4.15 の非可換再記述。H_* の模型のみ所有レーンから明示的に借りる。
使われ方：Proposition 4.14 の安定化前の有限 rank の零化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：基底をブロック和、列を右から a 倍して零埋めする有限 rank の対射。
方針：三角群への実右乗法と、証明済みの実因子化を合成する。
規約：KST Claim 4.15、通常の写像との同定は以下の二成分の式による。
使われ方：相対写像の零化と有限 rank の安定化。 -/
def claim415ColumnPairMap (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) (n m : ℕ) :=
  ((I.standardIdeal.rightColumnActionHom (I.standardElement a) n m).restrict
    (I.hatGLRepresentation n)).toPairMap.comp (claim415PairMap I n m)

/-- 概要：有限 rank の実対射の基底成分は通常の単位ブロック和。
方針：右乗法の実列の左上ブロックは恒等であることを使う。
規約：KST Claim 4.15。使われ方：原典の写像の基底成分との同定。 -/
lemma claim415ColumnPairMap_base (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (n m q : ℕ)
    (x : ActionProduct (I.hatGLSubmonoid n q)
      (Multiplicative (Fin n → integerUnitizationIdeal (I.obj (op ⦋q⦌))))) :
    (((claim415ColumnPairMap I a n m).total.app (op ⦋q⦌)).hom x).base =
      I.hatGLBlockHom n m q x.base := by
  apply Subtype.ext
  change (claim415FactorizationHom I n m q
      ⟨x.base, lastRightColumnHom n m (integerUnitizationIdeal (I.obj (op ⦋q⦌)))
        (I.standardIdeal.vertexElement (I.standardElement a) (op ⦋q⦌)).val x.fiber⟩).base.val =
    firstBlockMatrix n m x.base.val
  rw [claim415FactorizationHom_base, lastRightColumn_dropLast, one_mul]

/-- 概要：有限 rank の実対射の列成分は通常の右乗法の零埋め。
方針：三角群の実最終列の成分公式を合成射の列成分へ適用する。
規約：KST Claim 4.15 の v↦va。中心性・乗法単射性はこの有限 rank の零化には不要。
使われ方：原典の通常の相対写像との実同定。 -/
lemma claim415ColumnPairMap_fiber (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (n m q : ℕ)
    (x : ActionProduct (I.hatGLSubmonoid n q)
      (Multiplicative (Fin n → integerUnitizationIdeal (I.obj (op ⦋q⦌))))) :
    (((claim415ColumnPairMap I a n m).total.app (op ⦋q⦌)).hom x).fiber =
      Multiplicative.ofAdd (columnBlockInclusion (integerUnitizationIdeal (I.obj (op ⦋q⦌))) n m
        (idealVectorRightHom (integerUnitizationIdeal (I.obj (op ⦋q⦌))) (Fin n)
          (I.standardIdeal.vertexElement (I.standardElement a) (op ⦋q⦌)).val x.fiber).toAdd) := by
  change (claim415FactorizationHom I n m q
      ⟨x.base, lastRightColumnHom n m (integerUnitizationIdeal (I.obj (op ⦋q⦌)))
        (I.standardIdeal.vertexElement (I.standardElement a) (op ⦋q⦌)).val x.fiber⟩).fiber = _
  rw [claim415FactorizationHom_fiber, lastRightColumn_lastColumn]

/-- 概要：有限 rank の基底のブロック和と列の右乗法が誘導する相対写像は次数 ≤m で零。
方針：二成分の式で通常の写像と同定した実因子化の零化を使う。
規約：KST Claim 4.15、非単位非可換環。H_* の関手と自然な複体模型のみ明示する。
使われ方：Proposition 4.14 の安定化への有限 rank の入力。 -/
theorem claim415 (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) (n m : ℕ)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (hF : SSet.anodyneExtensions.IsInvertedBy F)
    {i : ℕ} (M : SimplicialHomologyModel F i) (hi : i ≤ m) :
    relativeBarPairMap F (claim415ColumnPairMap I a n m) = 0 :=
  claim415_factorized_relative_zero I a n m F hF M hi

end SerrePositivity.KST.ProExcision

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Claim 4.15" (partial := component) "仮定：非単位的単体環と頂点、i≤m、anodyne を反転するホモロジーの模型（Lean が強い）。結論：指定した相対 bar の列写像が零。原典の行列半直積の相対ホモロジーへの同定を別途要する（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.claim415
attribute [cite KST "Eq (4.4)" (partial := component) "仮定：中心元と非単位的単体環の列、ホモロジー模型（Lean が強い）。結論：中心倍イデアルの自然性と列に関する零化。安定 GL(ℤ) のホモロジー像への作用の自明性までは得ない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.claim415
attribute [cite KST "Eq (4.5)" (partial := component) "仮定：非単位的単体環と頂点、i≤m、anodyne を反転するホモロジーの模型（Lean が強い）。結論：指定した相対 bar の列写像が零。原典の行列半直積の相対ホモロジーへの同定を別途要する（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.claim415
attribute [cite KST "Prop 4.14" (partial := component) "仮定：中心元と非単位的単体環の列、ホモロジー模型（Lean が強い）。結論：中心倍イデアルの自然性と列に関する零化。安定 GL(ℤ) のホモロジー像への作用の自明性までは得ない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.claim415
