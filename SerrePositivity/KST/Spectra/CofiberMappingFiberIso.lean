module

public import SerrePositivity.KST.Spectra.CofiberMappingPullback
public import SerrePositivity.KST.Spectra.PointedFiber

/-!
概要：点つき cofiber からの写像空間を制限射の基点 fiber と同定する。
方針：cofiber の Hom の引き戻しを、点からの Hom が終対象である同型で移す。
規約：通常の単体集合の同型。単射性や Kan 性は同型の構成には不要。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の写像空間の塔の fiber。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：cofiber の Hom の引き戻しは制限射の定数基点上の引き戻しである。
方針：点からの Hom を終対象へ写し、下辺を基点の定数射と照合する。
規約：X、Y、Z は任意の点つき単体集合。
使われ方：Goerss–Jardine I §7、VIII §1。写像空間の fiber の商による表示。 -/
theorem cofiberMappingFiber_isPullback {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pointedCofiberProjection i) Z)
      (terminal.from (PointedObject.basedHom (pointedCofiber i) Z).right)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z)
      (SSet.const (X := ⊤_ SSet.{u})
        (PointedSimplicialSet.basepoint (PointedObject.basedHom X Z))) := by
  let T := PointedObject.basedHom (PointedObject.point : PointedSimplicialSet.{u}) Z
  let B : PointedSimplicialSet.{u} := PointedObject.basedHom X Z
  let e : T.right ≅ ⊤_ SSet.{u} := (homPointIsTerminal Z).uniqueUpToIso terminalIsTerminal
  have h := cofiberMapping_isPullback i Z
  refine h.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · exact Subsingleton.elim _ _
  · simp
  · let : IsIso T.hom := isIso_of_isTerminal isTerminalTensorUnit (homPointIsTerminal Z) _
    apply (cancel_epi T.hom).mp
    have hw : T.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedObject.toPoint X) Z = B.hom :=
      Under.w (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.toPoint X) Z)
    have hc : SSet.const (X := 𝟙_ SSet.{u}) B.basepoint = B.hom := by
      simpa only [toUnit_unit, Category.id_comp] using
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const B (𝟙_ SSet.{u})).symm
    exact hw.trans (by rw [SSet.comp_const, SSet.comp_const, hc])

/-- 概要：cofiber からの Hom と制限射の基点 fiber の実際の同型。
方針：基点上の引き戻しの普遍性を使う。
規約：KanFiber は L9b で構成した厳密な基点 fiber。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の塔の fiber の群の計算。 -/
def cofiberMappingFiberIso {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom (pointedCofiber i) Z).right ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z)
        (PointedSimplicialSet.basepoint (PointedObject.basedHom X Z)) :=
  (cofiberMappingFiber_isPullback i Z).isoPullback

@[reassoc]
lemma cofiberMappingFiberIso_hom_ι {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) :
    (cofiberMappingFiberIso i Z).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z)
          (PointedSimplicialSet.basepoint (PointedObject.basedHom X Z)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pointedCofiberProjection i) Z :=
  (cofiberMappingFiber_isPullback i Z).isoPullback_hom_fst

end

end SerrePositivity.KST.Spectra
