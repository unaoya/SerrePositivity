module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingJoinShapes
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SplitCoconeExtension

/-!
概要：全交互前置図式の分裂比較から、標準単体で表示した次段を構成する。
方針：coslice の辺を展開した join を標準単体同型で移送する。
規約：元の図式・増大余錐・次の偶数前置図式を全射として保持する。
使われ方：fiber の可算交互図式の再帰と貼り合わせ。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u}} {n : ℕ} {F : (Δ[2 * n] : SSet.{u}) ⟶ C}
  {c d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋0⦌} (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).Edge c d)

/-- 概要：二頂点を加えた全交互図式を次の標準単体上に置く。
方針：元の coslice 辺の全 uncurry を移送する。
規約：辺の高次成分を選び直さない。
使われ方：可算交互再帰の後続図式。 -/
def standardAlternatingExtension : (Δ[2 * (n + 1)] : SSet.{u}) ⟶ C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingSuccessorIso n).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (SSet.yonedaEquiv.symm e.edge)

/-- 概要：分裂三角形から次の標準交互図式の増大余錐を得る。
方針：join 上で構成済みの全余錐を同じ標準同型で制限する。
規約：元の分裂三角形を保持する。
使われ方：固定 fiber 頂点を保つ後続段。 -/
def standardAlternatingExtensionCocone {r : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).Edge d c}
    (T : e.CompStruct r (SSet.Edge.id c)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (standardAlternatingExtension e) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.splitCoconeExtension T).restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingSuccessorIso n).inv

/-- 概要：標準表示を join 表示へ戻すと元の全 uncurry になる。
方針：標準単体同型の相殺。
規約：全射の厳密な等式。
使われ方：各面の比較を共通の join で行う。 -/
lemma standardAlternatingExtension_join :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingSuccessorIso n).hom ≫ standardAlternatingExtension e =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (SSet.yonedaEquiv.symm e.edge) := by
  simp [standardAlternatingExtension]

/-- 概要：次段の増大余錐を join へ戻すと構成済みの分裂余錐になる。
方針：join の合成則で同型と逆同型を相殺する。
規約：全余錐を比較する。
使われ方：増大余錐の既存段への制限。 -/
lemma standardAlternatingExtensionCocone_join {r : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).Edge d c}
    (T : e.CompStruct r (SSet.Edge.id c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingSuccessorIso n).hom (𝟙 Δ[0]) ≫
      (standardAlternatingExtensionCocone e T).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.splitCoconeExtension T).val := by
  dsimp only [standardAlternatingExtensionCocone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.restrict]
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Iso.hom_inv_id, Category.id_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]

/-- 概要：次段の図式は全元図式を厳密に延長する。
方針：join 表示へ戻して uncurry の固定条件を使う。
規約：全前置単体の等式。
使われ方：全可算図式への貼り合わせ。 -/
lemma standardAlternatingExtension_old :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[2 * n] Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingSuccessorIso n).hom) ≫
      standardAlternatingExtension e = F := by
  rw [Category.assoc, standardAlternatingExtension_join, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed]

/-- 概要：次段の増大余錐も全元余錐を厳密に延長する。
方針：join 合成則と分裂余錐の元図式への制限を使う。
規約：頂点と脚のみでなく全余錐射を比較する。
使われ方：固定標的上の可算余錐への貼り合わせ。 -/
lemma standardAlternatingExtensionCocone_old {r : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).Edge d c}
    (T : e.CompStruct r (SSet.Edge.id c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[2 * n] Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingSuccessorIso n).hom) (𝟙 Δ[0]) ≫
      (standardAlternatingExtensionCocone e T).val = c.val := by
  rw [← Category.comp_id (𝟙 (Δ[0] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.assoc,
    standardAlternatingExtensionCocone_join]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.splitCoconeExtension_old_val T

/-- 概要：次段の偶数前置図式は新しい表示余錐の偶数制限そのもの。
方針：偶数面の join 式と辺の終点の uncurry を合成する。
規約：全偶数前置単体を同時に比較する。
使われ方：元の filtered 表示図式の後続段との整合。 -/
lemma standardAlternatingExtension_even :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace (n + 1)) ≫
      standardAlternatingExtension e =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n)) (𝟙 Δ[0]) ≫ d.val := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace_successor_join, Category.assoc,
    standardAlternatingExtension_join]
  rw [← Category.id_comp (SSet.stdSimplex.δ (0 : Fin 2)),
    ← Category.comp_id (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, e.δ_zero_yonedaEquiv_symm]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
