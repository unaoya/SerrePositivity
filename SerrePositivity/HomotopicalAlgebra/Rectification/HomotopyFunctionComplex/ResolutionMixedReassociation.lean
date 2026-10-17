module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedDiagram

/-!
# 中断した任意モデル源への一般化：ResolutionMixedReassociation

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual natural reassociation needed by the fourth selected interval。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0323][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0323
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual natural reassociation needed by the fourth selected interval
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedReassociation
variable (C : Type u) [Category.{v} C] [ModelCategory C]

abbrev leftFinal (p : Index C) := ResolutionArrowElementary.center p.source p.final
  ((p.pre.map.base ≫ p.center) ≫ p.post.base)

lemma assocEq (p : Index C) : leftFinal C p = d C p :=
  congrArg (ResolutionArrowElementary.center p.source p.final)
    (Category.assoc p.pre.map.base p.center p.post.base)

abbrev finalIso (p : Index C) : leftFinal C p ≅ d C p := eqToIso (assocEq C p)

lemma finalIso_hom (p : Index C) : (finalIso C p).hom.hom = (𝟙 _, 𝟙 _) := by
  change (Functor.Elements.π (ResolutionArrowDiagram.baseMaps C)).map
    (eqToHom (assocEq C p)) = _
  rw [eqToHom_map]
  rfl

lemma finalIso_inv (p : Index C) : (finalIso C p).inv.hom = (𝟙 _, 𝟙 _) := by
  change (Functor.Elements.π (ResolutionArrowDiagram.baseMaps C)).map
    (eqToHom (assocEq C p).symm) = _
  rw [eqToHom_map]
  rfl

/-- The left-associated final centers vary along exactly the transported actual cubes. -/
def finalLeft : Index C ⥤ ResolutionArrowDiagram.Index C where
  obj := leftFinal C
  map {p q} k := (finalIso C p).hom ≫ (cornerD C).map k ≫ (finalIso C q).inv
  map_id p := by
    rw [CategoryTheory.Functor.map_id]
    change (finalIso C p).hom ≫ (𝟙 (d C p)) ≫ (finalIso C p).inv = 𝟙 _
    rw [Category.id_comp, Iso.hom_inv_id]
  map_comp {p q r} f g := by
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Reassociation is an actual natural isomorphism of the two final-center diagrams. -/
def toFinal : finalLeft C ≅ cornerD C :=
  NatIso.ofComponents (finalIso C) (by
    intro p q k
    change ((finalIso C p).hom ≫ (cornerD C).map k ≫ (finalIso C q).inv) ≫
      (finalIso C q).hom = (finalIso C p).hom ≫ (cornerD C).map k
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

abbrev edgeBDLeft : cornerB C ⟶ finalLeft C := edgeBD C ≫ (toFinal C).inv

lemma edgeBDLeft_app (p : Index C) : (edgeBDLeft C).app p =
    ResolutionArrowElementary.post p.source p.target p.final
      (p.pre.map.base ≫ p.center) p.post := by
  apply Functor.Elements.hom_ext
  change (bd C p).hom ≫ (finalIso C p).inv.hom = _
  rw [finalIso_inv]
  apply Prod.ext
  · exact Category.id_comp _
  · exact Category.comp_id _

def postBD : Index C ⥤ SelectedIntervalDiagram.Index C where
  obj p := .post p.source p.target p.final (p.pre.map.base ≫ p.center) p.post
  map {p q} k := InducedCategory.homMk
    (Arrow.homMk ((cornerB C).map k) ((finalLeft C).map k) (by
      have h := (edgeBDLeft C).naturality k
      rw [edgeBDLeft_app, edgeBDLeft_app] at h
      exact h))
  map_id p := by
    apply InducedCategory.hom_ext
    apply Arrow.hom_ext
    · exact (cornerB C).map_id p
    · exact (finalLeft C).map_id p
  map_comp f g := by
    apply InducedCategory.hom_ext
    apply Arrow.hom_ext
    · exact (cornerB C).map_comp f g
    · exact (finalLeft C).map_comp f g

lemma post_cast (p : Index C) :
    ResolutionArrowElementary.post p.source p.target p.final (p.pre.map.base ≫ p.center) p.post ≫
      (finalIso C p).hom = bd C p := by
  apply (congrArg (fun k => k ≫ (finalIso C p).hom) (edgeBDLeft_app C p).symm).trans
  change ((bd C p ≫ (finalIso C p).inv) ≫ (finalIso C p).hom) = bd C p
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The small fiber transport is exactly the existing old castMap, including its base equality. -/
lemma fiber_cast (p : Index C) : (ResolutionArrowDiagram.fibers C).map (finalIso C p).hom =
    CoherentLiftMixedComparison.castMap p.source.inner p.middle.inner p.target p.final
      p.pre.map p.center p.post := by
  change (ResolutionArrowDiagram.fibers C).map (eqToHom (assocEq C p)) = _
  rw [eqToHom_map]
  rfl

lemma bd_fibers (p : Index C) : (ResolutionArrowDiagram.fibers C).map (bd C p) =
    CoherentLiftMixedComparison.postTail p.source.inner p.middle.inner p.target p.final
      p.pre.map p.center p.post := by
  rw [← post_cast C p, CategoryTheory.Functor.map_comp, ResolutionArrowElementary.post_fibers,
    fiber_cast]

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedReassociation
