module

public import SerrePositivity.KST.Spectra.PointedHomotopyGroupDiagram
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
概要：二以上の次数のホモトピー群の可換群・加法群の図式と余単体交代余面複体。
方針：充填で証明済みの可換群構造を使い、加法群への標準関手を後合成する。
規約：k は実際の次数 k+2。交代余面複体は Mathlib の通常の構成を使う。
使われ方：Goerss–Jardine I §7、VIII §2。Tot の cochain の代数的な係数の複体。
-/

@[expose] public section

universe u v w

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.KanHomotopyGroup

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J : Type v} [Category.{w} J]

/-- 概要：点つき Kan 図式の二以上の次数のホモトピー群の可換群の図式。
方針：可換性を加えた群と誘導準同型を束ねる。
規約：k は実際の次数 k+2。
使われ方：Goerss–Jardine I §7。余単体の加法的な cochain の係数。 -/
def commDiagram (D : J ⥤ PointedSimplicialSet.{u}) [∀ j, KanComplex (D.obj j).right] (k : ℕ) :
    J ⥤ CommGrpCat.{u} where
  obj j := CommGrpCat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (D.obj j).right (k + 1) (D.obj j).basepoint)
  map f := CommGrpCat.ofHom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := k + 1) (D.map f).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _))
  map_id j := by
    ext a
    change pointedHomotopyMap (k + 2) (D.map (𝟙 j)) a = a
    rw [D.map_id]
    exact pointedHomotopyMap_id _ _ _
  map_comp f g := by
    ext a
    change pointedHomotopyMap (k + 2) (D.map (f ≫ g)) a =
      pointedHomotopyMap (k + 2) (D.map g) (pointedHomotopyMap (k + 2) (D.map f) a)
    rw [D.map_comp]
    exact pointedHomotopyMap_comp _ _ _ _

def commDiagramMap {D E : J ⥤ PointedSimplicialSet.{u}}
    [∀ j, KanComplex (D.obj j).right] [∀ j, KanComplex (E.obj j).right]
    (τ : D ⟶ E) (k : ℕ) : commDiagram D k ⟶ commDiagram E k where
  app j := CommGrpCat.ofHom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := k + 1) (τ.app j).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _))
  naturality i j f := by
    ext a
    change pointedHomotopyMap (k + 2) (τ.app j) (pointedHomotopyMap (k + 2) (D.map f) a) =
      pointedHomotopyMap (k + 2) (E.map f) (pointedHomotopyMap (k + 2) (τ.app i) a)
    rw [← pointedHomotopyMap_comp, ← pointedHomotopyMap_comp, τ.naturality f]

def commDiagramIso {D E : J ⥤ PointedSimplicialSet.{u}}
    [∀ j, KanComplex (D.obj j).right] [∀ j, KanComplex (E.obj j).right]
    (e : D ≅ E) (k : ℕ) : commDiagram D k ≅ commDiagram E k :=
  NatIso.ofComponents
    (fun j ↦
      let ej : (D.obj j).right ≅ (E.obj j).right := PointedSimplicialSet.forget.mapIso (e.app j)
      MulEquiv.toCommGrpIso (X := (commDiagram D k).obj j) (Y := (commDiagram E k).obj j)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (k + 1) ej (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (e.app j).hom)))
    (fun f ↦ (commDiagramMap e.hom k).naturality f)

/-- 概要：高次ホモトピー群の図式を加法的可換群として表す。
方針：乗法的可換群から加法的可換群への標準関手を後合成する。
規約：k は実際の次数 k+2。
使われ方：Goerss–Jardine VIII §2。交代余面複体を形成する係数の図式。 -/
def additiveDiagram (D : J ⥤ PointedSimplicialSet.{u})
    [∀ j, KanComplex (D.obj j).right] (k : ℕ) : J ⥤ AddCommGrpCat.{u} :=
  commDiagram D k ⋙ CommGrpCat.toAddCommGrp

/-- 概要：余単体 Kan 図式の高次ホモトピー群の交代余面複体。
方針：加法的なホモトピー群の余単体図式に標準の交代余面複体を適用する。
規約：複体の次数とホモトピー次数 k+2 は別の添字。
使われ方：Goerss–Jardine VIII §2。Tot のホモトピー群の計算の代数的な cochain 複体。 -/
def cochainComplex (D : CosimplicialObject PointedSimplicialSet.{u})
    [∀ j, KanComplex (D.obj j).right] (k : ℕ) : CochainComplex AddCommGrpCat.{u} ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (additiveDiagram D k)

end

end SerrePositivity.KST.Spectra.KanHomotopyGroup
