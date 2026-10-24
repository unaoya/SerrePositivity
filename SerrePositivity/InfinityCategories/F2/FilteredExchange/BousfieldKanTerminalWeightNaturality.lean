module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.BousfieldKanTerminalWeight

/-!
概要：終対象による重みの収縮は反変添字の変更に厳密に自然。
方針：nerve のホモトピーの前後合成を、始対象に定値な関手からの射の一意性で比較する。
規約：選んだ終対象への射の等式は終対象性から得る。
使われ方：重み付き coend の収縮ホモトピーの dinaturality。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 概要：同じ始対象関手からの自然変換は、端点の表示によらず同じ nerve ホモトピーを与える。
方針：端点を等式で揃え、始対象性で二つの自然変換を同定する。
規約：射の実際の等式。使われ方：重みの収縮の自然性。 -/
lemma nerveNatTransHomotopy_h_eq_of_initial {A B : Type u} [SmallCategory A] [SmallCategory B]
    {F F' G G' : A ⥤ B} (η : F ⟶ G) (η' : F' ⟶ G')
    (hF : F = F') (hG : G = G') (h : IsInitial F) :
    (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy η).h = (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy η').h := by
  subst F'
  subst G'
  have he := h.hom_ext η η'
  subst η'
  rfl

variable {I : Type u} [SmallCategory I] {t : I}

/-- 概要：重みの始対象は Over の後合成で指定された始対象に移る。
方針：t への二つの合成射を終対象性で同定する。
規約：単体集合ではなく元の Over 圏の対象の等式。使われ方：定値関手の整合。 -/
lemma terminalWeightPoint_map (ht : IsTerminal t) {i j : I} (f : i ⟶ j) :
    (Over.map f.op).obj (terminalWeightPoint ht j) = terminalWeightPoint ht i := by
  change Over.mk ((ht.from j).op ≫ f.op) = Over.mk (ht.from i).op
  congr 1
  apply Quiver.Hom.unop_inj
  exact ht.hom_ext _ _

/-- 概要：指定した始点からの重みの収縮は添字に自然。
方針：nerve のホモトピーの whisker 自然性と、始対象関手からの射の一意性を使う。
規約：区間の向きと実際の円柱の射を保持する。使われ方：coend 上への降下。 -/
lemma terminalWeightHomotopy_naturality (ht : IsTerminal t) {i j : I} (f : i ⟶ j) :
    ((bousfieldKanWeight Iᵒᵖ).map f.op ▷ (Δ[1] : SSet.{u})) ≫
      (terminalWeightHomotopy ht i).h =
        (terminalWeightHomotopy ht j).h ≫ (bousfieldKanWeight Iᵒᵖ).map f.op := by
  change (nerveMap (Over.map f.op) ▷ (Δ[1] : SSet.{u})) ≫
    (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy (terminalWeightNatTrans ht i)).h =
      (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy (terminalWeightNatTrans ht j)).h ≫ nerveMap (Over.map f.op)
  rw [SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy_whiskerLeft, SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy_whiskerRight]
  apply nerveNatTransHomotopy_h_eq_of_initial
  · refine CategoryTheory.Functor.ext (fun _ ↦ (terminalWeightPoint_map ht f).symm) ?_
    intro X Y a
    simp
  · rfl
  · change IsInitial ((Functor.const (Over (Opposite.op j))).obj (terminalWeightPoint ht i))
    exact Functor.isInitialConst _ (terminalWeightPoint_isInitial ht i)

end SerrePositivity.InfinityCategories.F2
