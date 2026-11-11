module

public import SerrePositivity.KST.Spectra.PointedHomotopy
public import Mathlib.Algebra.Category.Grp.Basic

/-!
概要：任意の点つき Kan 図式の正次数ホモトピー群の図式と自然変換。
方針：基点を保つ射の誘導準同型と合成法則を群の圏へ束ねる。
規約：添字圏の filtered 性は要求せず、その宇宙も係数から独立にする。
使われ方：Goerss–Jardine I §7、VIII §2。余単体 cochain の π_* の群の図式。
-/

@[expose] public section

universe u v w

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.KanHomotopyGroup

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J : Type v} [Category.{w} J]

/-- 概要：任意の点つき Kan 図式に正次数のホモトピー群を適用する。
方針：各対象の群と各射の誘導準同型を使う。
規約：k は実際の次数 k+1。
使われ方：Goerss–Jardine I §7、VIII §2。余単体群の cochain 図式。 -/
def diagram (D : J ⥤ PointedSimplicialSet.{u}) [∀ j, KanComplex (D.obj j).right] (k : ℕ) :
    J ⥤ GrpCat.{u} where
  obj j := GrpCat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (D.obj j).right k (D.obj j).basepoint)
  map f := GrpCat.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := k) (D.map f).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _))
  map_id j := by
    ext a
    change pointedHomotopyMap (k + 1) (D.map (𝟙 j)) a = a
    rw [D.map_id]
    exact pointedHomotopyMap_id _ _ _
  map_comp f g := by
    ext a
    change pointedHomotopyMap (k + 1) (D.map (f ≫ g)) a =
      pointedHomotopyMap (k + 1) (D.map g) (pointedHomotopyMap (k + 1) (D.map f) a)
    rw [D.map_comp]
    exact pointedHomotopyMap_comp _ _ _ _

/-- 概要：点つき Kan 図式の自然変換は正次数ホモトピー群の自然変換を誘導する。
方針：各成分の誘導準同型と点つき合成の法則を使う。
規約：添字圏は任意。
使われ方：Goerss–Jardine VIII §2。cochain の図式の同型を π_* へ送る。 -/
def diagramMap {D E : J ⥤ PointedSimplicialSet.{u}}
    [∀ j, KanComplex (D.obj j).right] [∀ j, KanComplex (E.obj j).right]
    (τ : D ⟶ E) (k : ℕ) : diagram D k ⟶ diagram E k where
  app j := GrpCat.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := k) (τ.app j).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _))
  naturality i j f := by
    ext a
    change pointedHomotopyMap (k + 1) (τ.app j) (pointedHomotopyMap (k + 1) (D.map f) a) =
      pointedHomotopyMap (k + 1) (E.map f) (pointedHomotopyMap (k + 1) (τ.app i) a)
    rw [← pointedHomotopyMap_comp, ← pointedHomotopyMap_comp, τ.naturality f]

/-- 概要：点つき Kan 図式の同型は正次数ホモトピー群の群の図式の同型を誘導する。
方針：各成分の同型から群同型を作り、誘導準同型の自然性を使う。
規約：顔・退化への自然性を保持する。
使われ方：Goerss–Jardine VIII §2。非斉次 cochain への π_* の余単体比較。 -/
def diagramIso {D E : J ⥤ PointedSimplicialSet.{u}}
    [∀ j, KanComplex (D.obj j).right] [∀ j, KanComplex (E.obj j).right]
    (e : D ≅ E) (k : ℕ) : diagram D k ≅ diagram E k :=
  NatIso.ofComponents
    (fun j ↦
      let ej : (D.obj j).right ≅ (E.obj j).right := PointedSimplicialSet.forget.mapIso (e.app j)
      MulEquiv.toGrpIso (X := (diagram D k).obj j) (Y := (diagram E k).obj j)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso k ej (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (e.app j).hom)))
    (fun f ↦ (diagramMap e.hom k).naturality f)

end

end SerrePositivity.KST.Spectra.KanHomotopyGroup
