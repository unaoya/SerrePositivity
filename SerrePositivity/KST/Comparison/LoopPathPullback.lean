module

public import SerrePositivity.KST.Comparison.LoopPathRestriction

/-!
# loop の区間への制限の厳密なファイバー表示

概要：標準ループ空間は、基点始点 path space の終点の基点上の厳密なファイバーである。
方針：K-L9 の loopPathFiberIso を使い、包含を区間への制限と同定する。
規約：Segal 1974 Proposition 1.5 のファイバー比較。Kan 性はこの厳密な表示には不要。
使われ方：ホモトピーファイバーへの標準群完備化写像の可逆性の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory MonoidalClosed

/--
概要：K-L9 の loop と fiber の同型の包含は、標準円の区間への制限である。
方針：二つの円の同型と内部 Hom の反変な合成則を使う。
規約：同じ実際の単体的円を比較する。
使われ方：厳密な引き戻しの四角形の包含の同定。
-/
theorem loopPathFiberIso_hom_restriction (Y : PointedSimplicialSet.{u}) :
    (Spectra.loopPathFiberIso Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (Spectra.pathEndpoint Y).right Y.basepoint =
      loopPathRestriction Y := by
  rw [Spectra.loopPathFiberIso_hom_ι]
  change (((MonoidalClosed.pre Spectra.endpointCircleIso.{u}.hom).app Y) ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
      (Spectra.pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint) Y).right =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed intervalCircleProjection Y).right
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre,
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, ← NatTrans.comp_app, ← MonoidalClosed.pre_map]
  rfl

/--
概要：loop の区間への制限と終点評価の基点上の四角形は厳密な引き戻し。
方針：選択された fiber の引き戻しを、loop との実際の同型で移す。
規約：基底の点は終対象から選んだ基点への定数射。
使われ方：標準群完備化写像を厳密なファイバーへの比較として判定する。
-/
theorem loopPathRestriction_isPullback (Y : PointedSimplicialSet.{u}) :
    IsPullback (loopPathRestriction Y) (terminal.from (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right)
      (Spectra.pathEndpoint Y).right (SSet.const (X := ⊤_ SSet.{u}) Y.basepoint) := by
  let p := (Spectra.pathEndpoint Y).right
  let b := SSet.const (X := ⊤_ SSet.{u}) Y.basepoint
  refine (IsPullback.of_hasPullback p b).of_iso (Spectra.loopPathFiberIso Y).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by rfl) (by rfl)
  · change pullback.fst p b = (Spectra.loopPathFiberIso Y).inv ≫ loopPathRestriction Y
    rw [← loopPathFiberIso_hom_restriction, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rfl
  · exact terminalIsTerminal.hom_ext _ _

end SerrePositivity.KST.Comparison
