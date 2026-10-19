module
public import SerrePositivity.KST.ProExcision.StableColumnAffine
public import SerrePositivity.KST.ProExcision.StableBarRelativeMaps

/-!
# 実安定列側半直積の相対ホモロジー比較

概要：実安定列側相対 H_* と通常の有限 rank 相対項の実余極限を同定する。
方針：実標準包含の図式と既存の相対順序列を恒等成分で比較する。
規約：KST Proposition 4.14、SW92 Lemma 1.4。比較は全て実証明から構成する。
使われ方：実安定列側の右乗法の零化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits Comparison

/-- 概要：有限 rank の実標準包含の商図式と既存の実相対 rank 順序列の自然同型。
方針：恒等成分を取り、一座標遷移が同じ実商写像であることを定義から検証する。
規約：SW92 Lemma 1.4。使われ方：既存の実相対零化との接続。 -/
def NonUnitalSimplicialRing.columnAffineRelativeDiagramIso
    (I : NonUnitalSimplicialRing.{u}) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) :
    relativeModuleDiagram (Functor.whiskerRight I.columnAffineSectionNatTrans (monoidBarFunctor ⋙ F)) ≅
      I.relativeAffineRankSequence F := by
  let t : relativeModuleDiagram
      (Functor.whiskerRight I.columnAffineSectionNatTrans (monoidBarFunctor ⋙ F)) ⟶
      I.relativeAffineRankSequence F :=
    NatTrans.ofSequence (fun _ ↦ 𝟙 _) (by
      intro n
      rw [Category.comp_id, Category.id_comp]
      rw [show (I.relativeAffineRankSequence F).map (homOfLE (Nat.le_add_right n 1)) =
        relativeBarPairMap F (I.columnBlockOverHom n 1).toPairMap from
          Functor.ofSequence_map_homOfLE_succ _ _]
      dsimp only [relativeModuleDiagram]
      unfold relativeBarPairMap
      apply relativeModuleMap_eq_of_right_eq
      change F.map (monoidBarMap (I.columnAffineRankSequence.map
          (homOfLE (Nat.le_add_right n 1)))) = F.map (monoidBarMap (I.columnBlockOverHom n 1).total)
      rw [show I.columnAffineRankSequence.map (homOfLE (Nat.le_add_right n 1)) =
        (I.columnBlockOverHom n 1).total from Functor.ofSequence_map_homOfLE_succ _ _])
  exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ t.naturality f)

/-- 概要：実安定列側半直積の相対 bar ホモロジー。
方針：実安定 ĜL 包含の H_* の像による通常商を取る。
規約：KST Proposition 4.14。使われ方：実安定相対写像の始域・終域。 -/
def NonUnitalSimplicialRing.stableColumnAffineRelativeModule
    (I : NonUnitalSimplicialRing.{u}) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) : ModuleCat.{u} ℤ :=
  relativeModule (F.map (monoidBarMap I.stableColumnAffineSection))

/-- 概要：実安定列側相対 H_* と有限 rank の実相対余極限の実同型。
方針：実安定 bar の相対比較と有限相対図式の恒等成分の実同型を合成する。
規約：SW92 Lemma 1.4、KST Proposition 4.14。相対比較を新しい仮定にしない。
使われ方：実有限 rank 右乗法の零化の実安定 H_* への移送。 -/
def NonUnitalSimplicialRing.stableColumnAffineRelativeIso
    (I : NonUnitalSimplicialRing.{u}) (F : SSet.{u} ⥤ ModuleCat.{u} ℤ)
    {i : ℕ} (M : SimplicialHomologyModel F i) :
    I.stableColumnAffineRelativeModule F ≅ I.relativeAffineColimit F :=
  M.relativeBarSequentialColimitIso I.columnAffineSectionNatTrans ≪≫
    colim.mapIso (I.columnAffineRelativeDiagramIso F)

end SerrePositivity.KST.ProExcision
