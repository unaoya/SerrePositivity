module

public import SerrePositivity.KST.Spectra.FilteredPointedHomotopy

/-!
概要：点つき filtered diagram の段ごとの π_n 同型を余極限へ移す。
方針：ホモトピー類の図式の自然同型と余極限の普遍性を使う。
規約：ここでは指定した基点について主張し、全基点への拡張は別に行う。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。filtered Ω 条件の移送。
-/

@[expose] public section

universe v w u

open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：図式の自然同型と可換な二つの余極限の射は同型。
方針：逆自然変換から余極限の逆射を作り、両合成を各脚の後で計算する。
規約：任意の圏の通常の余極限の主張。
使われ方：HA §1.4.2、BF 1978 §2。π_n の図式の同型を余極限へ移す。 -/
def coconeIsoOfDiagramIso {I : Type w} [Category I] {C : Type u} [Category.{v} C]
    {F G : I ⥤ C} {c : Cocone F} {d : Cocone G} (hc : IsColimit c) (hd : IsColimit d)
    (e : F ≅ G) (f : c.pt ⟶ d.pt) (h : ∀ j, c.ι.app j ≫ f = e.hom.app j ≫ d.ι.app j) :
    c.pt ≅ d.pt where
  hom := f
  inv := hd.map c e.inv
  hom_inv_id := by
    apply hc.hom_ext
    intro j
    rw [← Category.assoc, h j, Category.assoc, IsColimit.ι_map,
      ← Category.assoc, e.hom_inv_id_app, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply hd.hom_ext
    intro j
    rw [← Category.assoc, IsColimit.ι_map, Category.assoc, h j,
      ← Category.assoc, e.inv_hom_id_app, Category.id_comp, Category.comp_id]

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  {D E : J ⥤ PointedSimplicialSet.{u}}
  [∀ j, KanComplex (D.obj j).right] [∀ j, KanComplex (E.obj j).right]

/-- 概要：点つき Kan 図式の自然変換はホモトピー類の図式の自然変換を誘導する。
方針：各段の誘導写像を使い、自然性を合成の関手性から示す。
規約：全自然数次数について型の図式の射を作る。
使われ方：Goerss–Jardine I §7、HA §1.4.2。filtered colimit への π_* 比較の移送。 -/
def pointedHomotopyDiagramMap (t : D ⟶ E) (n : ℕ) :
    pointedHomotopyDiagram D n ⟶ pointedHomotopyDiagram E n where
  app j := ↾(pointedHomotopyMap n (t.app j))
  naturality j k f := by
    ext a
    change pointedHomotopyMap n (t.app k) (pointedHomotopyMap n (D.map f) a) =
      pointedHomotopyMap n (E.map f) (pointedHomotopyMap n (t.app j) a)
    rw [← pointedHomotopyMap_comp, ← pointedHomotopyMap_comp, t.naturality f]

/-- 概要：段ごとの指定基点での π_n 同型は filtered colimit でも π_n 同型。
方針：各段の全単射を自然同型に束ね、二つのホモトピー類の余極限で比較する。
規約：零次数を含む。余極限の射の各脚での可換式を明示する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。Ω 条件の filtered colimit 保存。 -/
theorem pointedHomotopyMap_bijective_of_filtered {c : Cocone D} {d : Cocone E}
    [KanComplex c.pt.right] [KanComplex d.pt.right]
    (hc : IsColimit (PointedSimplicialSet.forget.mapCocone c))
    (hd : IsColimit (PointedSimplicialSet.forget.mapCocone d))
    (t : D ⟶ E) (g : c.pt ⟶ d.pt)
    (hg : ∀ j, c.ι.app j ≫ g = t.app j ≫ d.ι.app j)
    (ht : ∀ (j : J) (n : ℕ), Function.Bijective (pointedHomotopyMap n (t.app j))) (n : ℕ) :
    Function.Bijective (pointedHomotopyMap n g) := by
  let t' := pointedHomotopyDiagramMap t n
  let : ∀ j, IsIso (t'.app j) := fun j ↦ (isIso_iff_bijective _).2 (ht j n)
  let : IsIso t' := NatIso.isIso_of_isIso_app t'
  let e := asIso t'
  have h (j : J) : (pointedHomotopyCocone c n).ι.app j ≫ (↾(pointedHomotopyMap n g)) =
      e.hom.app j ≫ (pointedHomotopyCocone d n).ι.app j := by
    ext a
    change pointedHomotopyMap n g (pointedHomotopyMap (Y := c.pt) n (c.ι.app j) a) =
      pointedHomotopyMap (Y := d.pt) n (d.ι.app j) (pointedHomotopyMap n (t.app j) a)
    rw [← pointedHomotopyMap_comp (Z := d.pt), ← pointedHomotopyMap_comp (Z := d.pt), hg j]
  let i := coconeIsoOfDiagramIso (pointedHomotopyIsColimit c hc n)
    (pointedHomotopyIsColimit d hd n) e (↾(pointedHomotopyMap n g)) h
  exact (isIso_iff_bijective i.hom).1 inferInstance

end

end SerrePositivity.KST.Spectra
