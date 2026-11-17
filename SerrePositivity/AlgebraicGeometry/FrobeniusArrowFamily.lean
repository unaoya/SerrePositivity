module

public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowMapLaws
public import Mathlib.CategoryTheory.Limits.Fubini

/-!
概要：同じ環の矢印の族について、Frobenius の二変数図式と標準比較を作る。
方針：既存の矢印の写像の単位・合成則と余極限の自然性を適用する。
規約：有限段・実際の順極限・圏論的余極限の矢印を区別する。
使われ方：模型の filtered 極限と Frobenius 順極限の交換（計画 E01・E02・E03・E10）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- 元の矢印の族の、Frobenius 有限段の小さい二変数図式。 -/
def frobeniusArrowFamilyDiagram {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0) :
    J ⥤ (AsSmall.{u} ℕ ⥤ Arrow CommRingCat.{u}) where
  obj j := frobeniusArrowSmallDiagram (D.obj j) p hp (hL j) (hR j)
  map {j k} f := frobeniusArrowSmallDiagramMap (D.map f) p hp (hL j) (hR j) (hL k) (hR k)
  map_id j := by
    simpa only [D.map_id] using frobeniusArrowSmallDiagramMap_id p hp (hL j) (hR j)
  map_comp {i j k} f g := by
    simpa only [D.map_comp] using frobeniusArrowSmallDiagramMap_comp p hp (D.map f) (D.map g) (hL i) (hR i) (hL j) (hR j) (hL k) (hR k)

/-- 各矢印の実際の Frobenius 順極限を取った同じ族。 -/
def frobeniusArrowFamilyLimit {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0) :
    J ⥤ Arrow CommRingCat.{u} where
  obj j := Arrow.mk (CommRingCat.ofHom
    (frobeniusDirectLimitMap p hp (hL j) (hR j) (D.obj j).hom.hom))
  map {j k} f := frobeniusDirectLimitArrowMap (D.map f) p hp (hL j) (hR j) (hL k) (hR k)
  map_id j := by
    simpa only [D.map_id] using frobeniusDirectLimitArrowMap_id p hp (hL j) (hR j)
  map_comp {i j k} f g := by
    simpa only [D.map_comp] using frobeniusDirectLimitArrowMap_comp p hp (D.map f) (D.map g) (hL i) (hR i) (hL j) (hR j) (hL k) (hR k)

/-- 族の実際の順極限と圏論的余極限の、元の矢印に自然な標準同型。 -/
def frobeniusArrowFamilyStandardIso {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0) :
    frobeniusArrowFamilyLimit D p hp hL hR ≅
      frobeniusArrowFamilyDiagram D p hp hL hR ⋙ colim :=
  NatIso.ofComponents
    (fun j ↦ frobeniusArrowSmallColimitIso (D.obj j) p hp (hL j) (hR j))
    (by
      intro j k f
      exact frobeniusArrowSmallColimitIso_naturality (D.map f) p hp
        (hL j) (hR j) (hL k) (hR k))

/-- 同じ二変数図式の二つの順の余極限の Fubini 同型。 -/
def frobeniusArrowFamilyFubiniIso {J : Type u} [SmallCategory J]
    (D : J ⥤ Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hL : ∀ j, (p : (D.obj j).left) = 0) (hR : ∀ j, (p : (D.obj j).right) = 0) :
    colimit ((frobeniusArrowFamilyDiagram D p hp hL hR).flip ⋙ colim) ≅
      colimit (frobeniusArrowFamilyDiagram D p hp hL hR ⋙ colim) :=
  colimitFlipCompColimIsoColimitCompColim (frobeniusArrowFamilyDiagram D p hp hL hR)

end SerrePositivity.AlgebraicGeometry
