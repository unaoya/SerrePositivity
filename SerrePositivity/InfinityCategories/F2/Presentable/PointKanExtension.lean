module

public import SerrePositivity.InfinityCategories.F2.Presentable.TerminalKanColimit
public import SerrePositivity.InfinityCategories.F2.Presentable.LeftKanHomComposition

/-!
概要：元の全余極限を、一点の nerve への指定左 Kan 拡張として比較する。
方針：全ての局所添字の射影が同型であることから、F1B の局所存在定理を使う。
規約：一点の対象と射は同じ宇宙 u。余極限存在を Kan 普遍性の仮定に置き換えない。
使われ方：左 Kan 拡張を経由する二つの既存余極限の頂点比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 一点の通常の圏の指定対象は終対象。 -/
def pointKanTerminal (t : PUnit.{u + 1}) : IsTerminal t :=
  IsTerminal.ofUniqueHom (fun x ↦ homOfLE (le_of_eq (Subsingleton.elim x t)))
    (fun _ _ ↦ Subsingleton.elim _ _)

/-- 元の全図式の余極限が存在すれば、一点への任意の射に沿う左 Kan 拡張が存在する。 -/
lemma exists_pointLeftKanExtension {K X : SSet.{u}} [Quasicategory K] [Quasicategory X]
    (p : K ⟶ nerve PUnit.{u + 1}) (F : K ⟶ X) (hF : HasColimit F) :
    ∃ (G : nerve PUnit.{u + 1} ⟶ X) (β : SSet.Homotopy F (p ≫ G)),
      IsLeftKanExtension p F G β := by
  apply F1B.exists_kanLeftExtension_of_local_colimits p F
  intro v
  obtain ⟨t, rfl⟩ := nerveEquiv.symm.surjective v
  exact leftKanDiagram_nerveTerminal_hasColimit (pointKanTerminal t) p F hF

/-- 左 Kan 延長の前後で既に存在する二つの全余極限の頂点は同型。 -/
def leftKan_colimitVertexIso {A B X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X]
    (p : A ⟶ B) {F : A ⟶ X} {G : B ⟶ X}
    (β : SSet.Homotopy F (p ≫ G)) (hβ : IsLeftKanExtension p F G β)
    (c : JoinCocone F) (hc : IsColimitCone c)
    (d : JoinCocone G) (hd : IsColimitCone d) : VertexIso d.vertex c.vertex := by
  apply Classical.choice
  let q : B ⟶ nerve PUnit.{u + 1} := SSet.const (nerveVertex PUnit.unit)
  obtain ⟨L, α, hα⟩ := exists_pointLeftKanExtension q G ⟨d, hd⟩
  obtain ⟨M, γ, hγ⟩ := exists_pointLeftKanExtension (p ≫ q) F ⟨c, hc⟩
  let b := SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)
  let a := SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α)
  let g := SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy γ)
  let e := leftKanHomUniversalIso (p ≫ q) (leftKanCompositeUnit p q b a) g
    (leftKanHomUniversal_comp p q b a (F1B.kanLeftKanExtension_homUniversal p β hβ)
      (F1B.kanLeftKanExtension_homUniversal q α hα))
    (F1B.kanLeftKanExtension_homUniversal (p ≫ q) γ hγ)
  obtain ⟨cG, hcG, hvG⟩ := leftKan_nerveTerminal_colimitValue (pointKanTerminal PUnit.unit) hα
  obtain ⟨cF, hcF, hvF⟩ := leftKan_nerveTerminal_colimitValue (pointKanTerminal PUnit.unit) hγ
  have ev : VertexIso cG.vertex cF.vertex := by
    rw [hvG, hvF]
    exact e.toNatIso.app (HomotopyCategory.mk (nerveVertex PUnit.unit))
  exact ⟨colimitVertexIso d cG hd hcG ≪≫ ev ≪≫ colimitVertexIso cF c hcF hc⟩

end SerrePositivity.InfinityCategories.F2.Presentable
