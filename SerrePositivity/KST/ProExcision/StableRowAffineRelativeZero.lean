module
public import SerrePositivity.KST.ProExcision.StableRowAffineRelativeComparison

/-!
# 実安定行側相対ホモロジーにおける左乗法の零化

概要：実安定行側半直積の実左乗法が相対 H_* で零であることを証明する。
方針：実安定比較の自然性と、有限 rank の実相対余極限上の既証明の零化を合成する。
規約：KST Proposition 4.14、SW92 §1.2。零化を新しい仮定にしない。
使われ方：整数作用の像上での自明性への行側入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits Opposite
open scoped Simplicial

/-- 概要：行側の実左乗法の rank 自然変換は実標準包含を固定する。
方針：各有限 rank で実半直積写像の単位元保存を使う。
規約：SW92 §1.2。使われ方：実安定相対写像の正方形。 -/
lemma NonUnitalSimplicialRing.rowAffineLeftNatTrans_section
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌)) :
    I.rowAffineSectionNatTrans ≫ I.rowAffineLeftNatTrans a =
      (𝟙 I.hatGLRankSequence) ≫ I.rowAffineSectionNatTrans := by
  rw [Category.id_comp]
  apply NatTrans.ext
  funext n
  exact I.rowAffineLeftMap_section a n

/-- 概要：行側左乗法の実有限相対商図式の自然変換。
方針：実標準包含を固定する正方形を実 bar と H_* で写して実商へ降ろす。
規約：KST Proposition 4.14。使われ方：実安定比較の左乗法への自然性。 -/
def NonUnitalSimplicialRing.rowAffineLeftRelativeDiagramMap
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌))
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) :=
  relativeModuleDiagramMap (Functor.whiskerRight (𝟙 I.hatGLRankSequence) (monoidBarFunctor ⋙ F))
    (Functor.whiskerRight (I.rowAffineLeftNatTrans a) (monoidBarFunctor ⋙ F))
    (finiteBarHomologySquare F _ _ (I.rowAffineLeftNatTrans_section a))

/-- 概要：有限 rank の相対図式の実同型は実左乗法と可換。
方針：各成分の通常商の代表元で二つの実写像を直接評価する。
規約：SW92 Lemma 1.4。使われ方：既証明の実相対余極限零化との接続。 -/
lemma NonUnitalSimplicialRing.rowAffineRelativeDiagramIso_left
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌))
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (M : SimplicialHomologyModel F i) :
    I.rowAffineLeftRelativeDiagramMap a F ≫ (I.rowAffineRelativeDiagramIso F).hom =
      (I.rowAffineRelativeDiagramIso F).hom ≫ I.relativeRowAffineLeftNatTrans a F M := by
  apply NatTrans.ext
  funext n
  change (I.rowAffineLeftRelativeDiagramMap a F).app n ≫ 𝟙 _ =
    𝟙 _ ≫ (I.relativeRowAffineLeftNatTrans a F M).app n
  rw [I.relativeRowAffineLeftNatTrans_app, Category.id_comp, Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

/-- 概要：実安定行側相対 H_* に左乗法が誘導する実写像。
方針：実 rank 自然変換の実安定写像と実基底恒等射を相対商へ降ろす。
規約：KST Proposition 4.14。零性を定義に含めない。
使われ方：実安定相対零化の対象。 -/
def NonUnitalSimplicialRing.stableRowAffineRelativeLeftMap
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌))
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) :
    I.stableRowAffineRelativeModule F ⟶ I.stableRowAffineRelativeModule F :=
  relativeStableBarMap F (𝟙 I.hatGLRankSequence) (I.rowAffineLeftNatTrans a)
    (I.rowAffineLeftNatTrans_section a)

/-- 概要：実安定行側相対比較は実左乗法に可換。
方針：実安定相対 bar 比較の自然性と有限相対図式の実同型の自然性を合成する。
規約：SW92 Lemma 1.4、KST Proposition 4.14。
使われ方：有限 rank の実零化を実安定相対 H_* に移す。 -/
lemma NonUnitalSimplicialRing.stableRowAffineRelativeIso_left
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌))
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (M : SimplicialHomologyModel F i) :
    I.stableRowAffineRelativeLeftMap a F ≫ (I.stableRowAffineRelativeIso F M).hom =
      (I.stableRowAffineRelativeIso F M).hom ≫ I.relativeRowAffineLeftColimitMap a F M := by
  have hn := M.relativeBarSequentialColimitIso_natural
    (𝟙 I.hatGLRankSequence) (I.rowAffineLeftNatTrans a) (I.rowAffineLeftNatTrans_section a)
  have hc : colimMap (I.rowAffineLeftRelativeDiagramMap a F) ≫
      (colim.mapIso (I.rowAffineRelativeDiagramIso F)).hom =
    (colim.mapIso (I.rowAffineRelativeDiagramIso F)).hom ≫ I.relativeRowAffineLeftColimitMap a F M := by
    change colim.map (I.rowAffineLeftRelativeDiagramMap a F) ≫
        colim.map (I.rowAffineRelativeDiagramIso F).hom =
      colim.map (I.rowAffineRelativeDiagramIso F).hom ≫ colim.map (I.relativeRowAffineLeftNatTrans a F M)
    rw [← colim.map_comp, ← colim.map_comp, I.rowAffineRelativeDiagramIso_left a F M]
  change relativeStableBarMap F (𝟙 I.hatGLRankSequence) (I.rowAffineLeftNatTrans a)
      (I.rowAffineLeftNatTrans_section a) ≫
      ((M.relativeBarSequentialColimitIso I.rowAffineSectionNatTrans).hom ≫ _) =
    ((M.relativeBarSequentialColimitIso I.rowAffineSectionNatTrans).hom ≫ _) ≫ _
  dsimp only [rowAffineLeftRelativeDiagramMap] at hc
  rw [← Category.assoc, hn, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ (M.relativeBarSequentialColimitIso I.rowAffineSectionNatTrans).hom ≫ t) hc

/-- 概要：実安定行側相対 H_* 上の実左乗法は零。
方針：実安定比較を合成し、実有限 rank 余極限上で既証明の零化を使う。
規約：KST Proposition 4.14 の行側入力、SW92 §1.2。
使われ方：実アフィン共役から像上の整数作用への移送。 -/
theorem NonUnitalSimplicialRing.stableRowAffineRelativeLeftMap_zero
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌))
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) (hF : SSet.anodyneExtensions.IsInvertedBy F)
    {i : ℕ} (M : SimplicialHomologyModel F i) :
    I.stableRowAffineRelativeLeftMap a F = 0 := by
  apply (cancel_mono (I.stableRowAffineRelativeIso F M).hom).1
  rw [Limits.zero_comp, I.stableRowAffineRelativeIso_left,
    I.relativeRowAffineLeftColimitMap_zero a F hF M, Limits.comp_zero]

end SerrePositivity.KST.ProExcision
