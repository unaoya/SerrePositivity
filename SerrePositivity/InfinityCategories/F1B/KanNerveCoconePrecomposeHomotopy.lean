module

public import SerrePositivity.InfinityCategories.F1B.KanCoconePrecomposeNatTrans
public import SerrePositivity.InfinityCategories.F1B.KanNerveNatTransHomotopyFixedPoint

/-!
概要：指定自然変換による余錐の前合成を実ホモトピーで表示する。
方針：WithTerminal 上の拡張関手のホモトピーを標準余錐に沿って制限する。
規約：元の図式の指定変換と余錐の頂点を保持する。
使われ方：B5 の指定単位の左 Kan 局所輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F G : I ⥤ C}

/-- 概要：余錐の脚の前合成を元の join の余錐のホモトピーとして表す。
方針：終対象を付加した関手の自然変換を join に制限する。
規約：元の指定変換と頂点を全時間で保持する。
使われ方：B5 の指定単位に沿う左 Kan の局所輸送。 -/
def kanNerveCoconePrecomposeHomotopy (c : Cocone G) (η : F ⟶ G) :
    SSet.Homotopy (kanNerveCoconeEquiv ((Cocone.precompose η).obj c)).val
      (kanNerveCoconeEquiv c).val where
  h := (kanTerminalJoinNerveMap I ▷ (Δ[1] : SSet.{u})) ≫
    (kanNerveNatTransHomotopy (kanCoconePrecomposeNatTrans c η)).h
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, SSet.Homotopy.h₀,
      kanNerveCocone_withTerminal]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, SSet.Homotopy.h₁,
      kanNerveCocone_withTerminal]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 概要：余錐のホモトピーは元の図式上で指定自然変換に一致する。
方針：終対象を付加した関手の自然変換を join に制限する。
規約：元の指定変換と頂点を全時間で保持する。
使われ方：B5 の指定単位に沿う左 Kan の局所輸送。 -/
lemma kanNerveCoconePrecomposeHomotopy_diagram (c : Cocone G) (η : F ⟶ G) :
    (joinInl (nerve I) (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (kanNerveCoconePrecomposeHomotopy c η).h =
      (kanNerveNatTransHomotopy η).h := by
  change (joinInl (nerve I) (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
    (kanTerminalJoinNerveMap I ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [← Category.assoc, ← comp_whiskerRight]
  change ((joinInl (nerve I) (Δ[0] : SSet.{u}) ≫
    (kanNerveCoconeEquiv (kanWithTerminalCocone I)).val) ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [(kanNerveCoconeEquiv (kanWithTerminalCocone I)).property,
    kanNerveNatTransHomotopy_whiskerLeft, kanCoconePrecomposeNatTrans_restrict]

/-- 概要：余錐の脚の前合成ホモトピーは元の指定頂点で時間に定値。
方針：終対象を付加した関手の自然変換を join に制限する。
規約：元の指定変換と頂点を全時間で保持する。
使われ方：B5 の指定単位に沿う左 Kan の局所輸送。 -/
lemma kanNerveCoconePrecomposeHomotopy_fixedVertex (c : Cocone G) (η : F ⟶ G) :
    (joinInr (nerve I) (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      (kanNerveCoconePrecomposeHomotopy c η).h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        joinInr (nerve I) (Δ[0] : SSet.{u}) ≫ (kanNerveCoconeEquiv c).val := by
  change (joinInr (nerve I) (Δ[0] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
    (kanTerminalJoinNerveMap I ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [← Category.assoc, ← comp_whiskerRight]
  change ((joinInr (nerve I) (Δ[0] : SSet.{u}) ≫
    (kanNerveCoconeEquiv (kanWithTerminalCocone I)).val) ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [kanNerveCocone_point, kanNerveCocone_point]
  exact kanNerveNatTransHomotopy_fixedPoint (kanCoconePrecomposeNatTrans c η)
    (WithTerminal.star : WithTerminal I) c.pt rfl

end SerrePositivity.InfinityCategories.F1B
