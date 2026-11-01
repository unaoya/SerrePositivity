module

public import SerrePositivity.EInfinity.FrameHom.TerminalFiberBaseHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.NerveCoconePrism
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.NatTransHomotopyNaturality
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.OverCanonicalCocone
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.ConeFamilyUnderlying

/-!
# 元の Over 図式から恒等射への標準全ホモトピー

概要：元の Over 図式を恒等射へ送る唯一の自然変換と実円柱を保持する。
方針：Over の標準終対象から自然変換を作り、忘却像を元の余錐と同定する。
規約：全単体・元の構造射を保つ。
使われ方：実評価の底円柱と標準評価の全関手圏での比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory Limits Opposite SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (n : C) (T : I ⥤ Over n)

def overTerminalTransformation : T ⟶ (Functor.const I).obj (Over.mk (𝟙 n)) where
  app s := Over.mkIdTerminal.from (T.obj s)
  naturality {_ _} _ := Over.mkIdTerminal.hom_ext _ _

def overTerminalHomotopy : SSet.Homotopy (nerveMap T)
    (SSet.const (X := nerve I) (nerveVertex (Over.mk (𝟙 n)))) :=
  stableHomotopyRetarget (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy (overTerminalTransformation n T))
    rfl (SerrePositivity.InfinityCategories.F1B.nerveMap_const I (Over.mk (𝟙 n)))

lemma overTerminalTransformation_forget :
    Functor.whiskerRight (overTerminalTransformation n T) (Over.forget n) =
      ((SerrePositivity.InfinityCategories.F1B.overForgetCocone n).whisker T).ι := by
  apply NatTrans.ext
  funext s
  exact Over.mkIdTerminal_from_left (T.obj s)

lemma overTerminalHomotopy_forget_h : (overTerminalHomotopy n T).h ≫
    nerveMap (Over.forget n) =
      (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy ((SerrePositivity.InfinityCategories.F1B.overForgetCocone n).whisker T).ι).h := by
  change (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy (overTerminalTransformation n T)).h ≫ _ = _
  rw [SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy_whiskerRight, overTerminalTransformation_forget]

lemma overTerminalHomotopy_map_forget_h {D : Type u} [Category.{u} D] (G : C ⥤ D) :
    (overTerminalHomotopy n T).h ≫ nerveMap (Over.forget n) ≫ nerveMap G =
      (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy
        (G.mapCocone ((SerrePositivity.InfinityCategories.F1B.overForgetCocone n).whisker T)).ι).h := by
  rw [← Category.assoc, overTerminalHomotopy_forget_h]
  rw [← nerveCoconePrism_eq_natTrans (T ⋙ Over.forget n)
    ((SerrePositivity.InfinityCategories.F1B.overForgetCocone n).whisker T),
    ← nerveCoconePrism_eq_natTrans ((T ⋙ Over.forget n) ⋙ G)
      (G.mapCocone ((SerrePositivity.InfinityCategories.F1B.overForgetCocone n).whisker T))]
  simp only [Category.assoc]
  rw [SerrePositivity.InfinityCategories.F1B.nerveCocone_mapCocone]

end SerrePositivity.EInfinity.FrameHom
