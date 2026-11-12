module

public import SerrePositivity.KST.Spectra.FilteredPointedHomotopy
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
概要：正次数のホモトピー群と点つき Kan 複体の filtered colimit の可換性。
方針：群準同型の図式と cocone を作り、集合の余極限の普遍性を群へ戻す。
規約：添字 n は実際の次数 n+1。π_1 の非可換性も許す。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。L9d の有理化の群の計算。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (D : J ⥤ PointedSimplicialSet.{u}) [∀ j, KanComplex (D.obj j).right]

/-- 概要：点つき Kan 図式の各段の正次数ホモトピー群の図式。
方針：各段の群と、点つき射による誘導準同型を使う。
規約：n は実際の次数 n+1。
使われ方：Goerss–Jardine I §7、HA §1.4.2。π_* の filtered colimit の群の図式。 -/
def pointedHomotopyGroupDiagram (n : ℕ) : J ⥤ GrpCat.{u} where
  obj j := GrpCat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (D.obj j).right n (D.obj j).basepoint)
  map f := GrpCat.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (D.map f).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _))
  map_id j := by
    ext a
    change pointedHomotopyMap (n + 1) (D.map (𝟙 j)) a = a
    rw [D.map_id]
    exact pointedHomotopyMap_id _ _ _
  map_comp f g := by
    ext a
    change pointedHomotopyMap (n + 1) (D.map (f ≫ g)) a =
      pointedHomotopyMap (n + 1) (D.map g) (pointedHomotopyMap (n + 1) (D.map f) a)
    rw [D.map_comp]
    exact pointedHomotopyMap_comp _ _ _ _

/-- 概要：正次数のホモトピー群の filtered diagram は群の余極限を持つ。
方針：群の filtered colimit の既存の実構成を使う。
規約：非可換な π_1 にも適用する。
使われ方：Goerss–Jardine I §7、HA §1.4.2。群の余極限比較の始域。 -/
instance pointedHomotopyGroupDiagram_hasColimit (n : ℕ) :
    HasColimit (pointedHomotopyGroupDiagram D n) :=
  ⟨_, GrpCat.FilteredColimits.colimitCoconeIsColimit.{u, u} (pointedHomotopyGroupDiagram D n)⟩

variable {D} (c : Cocone D) [KanComplex c.pt.right]

/-- 概要：点つき cocone の正次数ホモトピー群の cocone。
方針：cocone 射が誘導する群準同型を脚とする。
規約：可換群とは限らない群の圏を使う。
使われ方：Goerss–Jardine I §7、HA §1.4.2。正次数の余極限比較。 -/
def pointedHomotopyGroupCocone (n : ℕ) : Cocone (pointedHomotopyGroupDiagram D n) where
  pt := GrpCat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup c.pt.right n c.pt.basepoint)
  ι := {
    app j := GrpCat.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (X := (D.obj j).right) (Y := c.pt.right)
      (n := n) (c.ι.app j).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _))
    naturality j k f := by
      ext a
      change pointedHomotopyMap (Y := c.pt) (n + 1) (c.ι.app k)
        (pointedHomotopyMap (n + 1) (D.map f) a) =
          pointedHomotopyMap (Y := c.pt) (n + 1) (c.ι.app j) a
      rw [← pointedHomotopyMap_comp (Z := c.pt), c.w f] }

/-- 概要：点つき Kan 図式の正次数ホモトピー群の cocone は群の余極限。
方針：忘却後の全自然数次数の余極限の普遍性を、忘却の同型反映で群へ戻す。
規約：基礎単体集合の cocone の余極限性を明示する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。有理化の π_* 計算。 -/
def pointedHomotopyGroupIsColimit
    (hc : IsColimit (PointedSimplicialSet.forget.mapCocone c)) (n : ℕ) :
    IsColimit (pointedHomotopyGroupCocone c n) := by
  let : ReflectsColimit (pointedHomotopyGroupDiagram D n) (forget GrpCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget GrpCat.{u})
  change IsColimit (pointedHomotopyCocone c (n + 1))
  exact pointedHomotopyIsColimit c hc (n + 1)

/-- 概要：段の正次数ホモトピー群の余極限と、点つき Kan 余極限の群との標準同型。
方針：群の二つの余極限の普遍性を比較する。
規約：群の圏の同型であり、誘導準同型を成分に持つ。
使われ方：Goerss–Jardine I §7、HA §1.4.2。telescope の π_* と群の有理化の比較。 -/
def pointedHomotopyGroupColimitIso
    (hc : IsColimit (PointedSimplicialSet.forget.mapCocone c)) (n : ℕ) :
    colimit (pointedHomotopyGroupDiagram D n) ≅
      GrpCat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup c.pt.right n c.pt.basepoint) :=
  (colimit.isColimit (pointedHomotopyGroupDiagram D n)).coconePointUniqueUpToIso
    (pointedHomotopyGroupIsColimit c hc n)

/-- 概要：群の余極限比較同型を各段へ制限すると元の cocone 射の誘導準同型。
方針：二つの余極限の標準比較同型の成分計算を使う。
規約：n は実際の次数 n+1。
使われ方：Goerss–Jardine I §7、HA §1.4.2。telescope への各段の写像の計算。 -/
@[reassoc (attr := simp)]
theorem pointedHomotopyGroupColimitIso_ι
    (hc : IsColimit (PointedSimplicialSet.forget.mapCocone c)) (n : ℕ) (j : J) :
    colimit.ι (pointedHomotopyGroupDiagram D n) j ≫
      (pointedHomotopyGroupColimitIso c hc n).hom =
        GrpCat.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (X := (D.obj j).right) (Y := c.pt.right)
          (n := n) (c.ι.app j).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j

/-- 概要：選ばれた点つき Kan 余極限の正次数群と段の群の余極限との標準同型。
方針：基点忘却が filtered colimit を保存することを一般の群比較へ適用する。
規約：元の cocone の余極限性は自動で証明する。
使われ方：BF 1978 §2、Goerss–Jardine I §7、HA §1.4.2。L9d の段ごとの群の計算。 -/
def filteredPointedHomotopyGroupIso (D : J ⥤ PointedSimplicialSet.{u})
    [∀ j, KanComplex (D.obj j).right] (n : ℕ) :
    colimit (pointedHomotopyGroupDiagram D n) ≅
      GrpCat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (colimit D).right n (colimit D).basepoint) :=
  by
    let : KanComplex (colimit.cocone D).pt.right :=
      inferInstanceAs (KanComplex (colimit D).right)
    exact pointedHomotopyGroupColimitIso (colimit.cocone D)
      (isColimitOfPreserves PointedSimplicialSet.forget (colimit.isColimit D)) n

/-- 概要：選ばれた点つき余極限の群比較を各段に制限すると余極限射の誘導準同型。
方針：一般の cocone に対する成分計算を選ばれた余極限へ適用する。
規約：n は実際の次数 n+1。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の余極限比較の成分計算。 -/
@[reassoc (attr := simp)]
theorem filteredPointedHomotopyGroupIso_ι (D : J ⥤ PointedSimplicialSet.{u})
    [∀ j, KanComplex (D.obj j).right] (n : ℕ) (j : J) :
    colimit.ι (pointedHomotopyGroupDiagram D n) j ≫ (filteredPointedHomotopyGroupIso D n).hom =
      GrpCat.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (colimit.ι D j).right
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)) := by
  let : KanComplex (colimit.cocone D).pt.right := inferInstanceAs (KanComplex (colimit D).right)
  exact pointedHomotopyGroupColimitIso_ι (colimit.cocone D)
    (isColimitOfPreserves PointedSimplicialSet.forget (colimit.isColimit D)) n j

end

end SerrePositivity.KST.Spectra
