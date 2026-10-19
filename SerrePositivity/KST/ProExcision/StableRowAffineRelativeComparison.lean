module
public import SerrePositivity.KST.ProExcision.StableRowAffine
public import SerrePositivity.KST.ProExcision.RelativeRowAffineLeftZero
public import SerrePositivity.KST.ProExcision.StableBarRelativeMaps

/-!
# 実安定行側相対ホモロジーと有限 rank の実相対余極限

概要：実行側の標準包含の相対 H_* を通常の有限 rank 相対項の実余極限と同定する。
方針：実相対商図式と通常の行側順序列を恒等成分で比較する。
規約：KST Proposition 4.14、SW92 Lemma 1.4。新しい比較仮定は不要。
使われ方：実行側左乗法の零化の実安定相対 H_* への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits Comparison

/-- 概要：有限 rank の行側の実相対商図式と通常の実相対順序列の自然同型。
方針：恒等成分を取り、通常の一座標遷移の実右側写像の一致を用いる。
規約：SW92 Lemma 1.4。使われ方：既存の行側実余極限零化との接続。 -/
def NonUnitalSimplicialRing.rowAffineRelativeDiagramIso
    (I : NonUnitalSimplicialRing.{u}) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) :
    relativeModuleDiagram (Functor.whiskerRight I.rowAffineSectionNatTrans (monoidBarFunctor ⋙ F)) ≅
      I.relativeRowAffineRankSequence F := by
  let t : relativeModuleDiagram
      (Functor.whiskerRight I.rowAffineSectionNatTrans (monoidBarFunctor ⋙ F)) ⟶
      I.relativeRowAffineRankSequence F :=
    NatTrans.ofSequence (fun _ ↦ 𝟙 _) (by
      intro n
      rw [Category.comp_id, Category.id_comp]
      rw [show (I.relativeRowAffineRankSequence F).map (homOfLE (Nat.le_add_right n 1)) =
        I.relativeRowAffineBlockMap n 1 F from Functor.ofSequence_map_homOfLE_succ _ _]
      dsimp only [relativeModuleDiagram]
      unfold relativeRowAffineBlockMap
      apply relativeModuleMap_eq_of_right_eq
      change F.map (monoidBarMap (I.rowAffineRankSequence.map
          (homOfLE (Nat.le_add_right n 1)))) = F.map (monoidBarMap (I.rowAffineBlockMap n 1))
      rw [show I.rowAffineRankSequence.map (homOfLE (Nat.le_add_right n 1)) =
        I.rowAffineBlockMap n 1 from Functor.ofSequence_map_homOfLE_succ _ _])
  exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ t.naturality f)

/-- 概要：実安定行側半直積の相対 bar ホモロジー。
方針：実安定 ĜL 包含の H_* の実像による通常商を取る。
規約：KST Proposition 4.14。使われ方：実安定行側相対写像の始域・終域。 -/
def NonUnitalSimplicialRing.stableRowAffineRelativeModule
    (I : NonUnitalSimplicialRing.{u}) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) : ModuleCat.{u} ℤ :=
  relativeModule (F.map (monoidBarMap I.stableRowAffineSection))

/-- 概要：実安定行側相対 H_* と有限 rank の実相対余極限の実同型。
方針：実安定相対比較と有限相対図式の実恒等同型の余極限を合成する。
規約：SW92 Lemma 1.4、KST Proposition 4.14。比較を仮定に隠さない。
使われ方：行側の実左乗法の安定零化。 -/
def NonUnitalSimplicialRing.stableRowAffineRelativeIso
    (I : NonUnitalSimplicialRing.{u}) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    {i : ℕ} (M : SimplicialHomologyModel F i) :
    I.stableRowAffineRelativeModule F ≅ I.relativeRowAffineColimit F :=
  M.relativeBarSequentialColimitIso I.rowAffineSectionNatTrans ≪≫
    colim.mapIso (I.rowAffineRelativeDiagramIso F)

end SerrePositivity.KST.ProExcision
