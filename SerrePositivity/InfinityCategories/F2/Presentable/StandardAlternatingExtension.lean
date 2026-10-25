module

public import SerrePositivity.InfinityCategories.F2.Presentable.AlternatingJoinShapes
public import SerrePositivity.InfinityCategories.F2.Presentable.SplitCoconeExtension

/-!
概要：全交互前置図式の分裂比較から、標準単体で表示した次段を構成する。
方針：coslice の辺を展開した join を標準単体同型で移送する。
規約：元の図式・増大余錐・次の偶数前置図式を全射として保持する。
使われ方：fiber の可算交互図式の再帰と貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {C : SSet.{u}} {n : ℕ} {F : (Δ[2 * n] : SSet.{u}) ⟶ C}
  {c d : (sliceUnder F) _⦋0⦌} (e : (sliceUnder F).Edge c d)

/-- 概要：二頂点を加えた全交互図式を次の標準単体上に置く。
方針：元の coslice 辺の全 uncurry を移送する。
規約：辺の高次成分を選び直さない。
使われ方：可算交互再帰の後続図式。 -/
def standardAlternatingExtension : (Δ[2 * (n + 1)] : SSet.{u}) ⟶ C :=
  (alternatingSuccessorIso n).inv ≫ sliceUnderUncurry (SSet.yonedaEquiv.symm e.edge)

/-- 概要：分裂三角形から次の標準交互図式の増大余錐を得る。
方針：join 上で構成済みの全余錐を同じ標準同型で制限する。
規約：元の分裂三角形を保持する。
使われ方：固定 fiber 頂点を保つ後続段。 -/
def standardAlternatingExtensionCocone {r : (sliceUnder F).Edge d c}
    (T : e.CompStruct r (SSet.Edge.id c)) : JoinCocone (standardAlternatingExtension e) :=
  (splitCoconeExtension T).restrict (alternatingSuccessorIso n).inv

/-- 概要：標準表示を join 表示へ戻すと元の全 uncurry になる。
方針：標準単体同型の相殺。
規約：全射の厳密な等式。
使われ方：各面の比較を共通の join で行う。 -/
lemma standardAlternatingExtension_join :
    (alternatingSuccessorIso n).hom ≫ standardAlternatingExtension e =
      sliceUnderUncurry (SSet.yonedaEquiv.symm e.edge) := by
  simp [standardAlternatingExtension]

/-- 概要：次段の増大余錐を join へ戻すと構成済みの分裂余錐になる。
方針：join の合成則で同型と逆同型を相殺する。
規約：全余錐を比較する。
使われ方：増大余錐の既存段への制限。 -/
lemma standardAlternatingExtensionCocone_join {r : (sliceUnder F).Edge d c}
    (T : e.CompStruct r (SSet.Edge.id c)) :
    joinMap (alternatingSuccessorIso n).hom (𝟙 Δ[0]) ≫
      (standardAlternatingExtensionCocone e T).val = (splitCoconeExtension T).val := by
  dsimp only [standardAlternatingExtensionCocone, JoinCocone.restrict]
  rw [← Category.assoc, ← joinMap_comp, Iso.hom_inv_id, Category.id_comp,
    joinMap_id, Category.id_comp]

/-- 概要：次段の図式は全元図式を厳密に延長する。
方針：join 表示へ戻して uncurry の固定条件を使う。
規約：全前置単体の等式。
使われ方：全可算図式への貼り合わせ。 -/
lemma standardAlternatingExtension_old :
    (joinInl Δ[2 * n] Δ[1] ≫ (alternatingSuccessorIso n).hom) ≫
      standardAlternatingExtension e = F := by
  rw [Category.assoc, standardAlternatingExtension_join, sliceUnderUncurry_fixed]

/-- 概要：次段の増大余錐も全元余錐を厳密に延長する。
方針：join 合成則と分裂余錐の元図式への制限を使う。
規約：頂点と脚のみでなく全余錐射を比較する。
使われ方：固定標的上の可算余錐への貼り合わせ。 -/
lemma standardAlternatingExtensionCocone_old {r : (sliceUnder F).Edge d c}
    (T : e.CompStruct r (SSet.Edge.id c)) :
    joinMap (joinInl Δ[2 * n] Δ[1] ≫ (alternatingSuccessorIso n).hom) (𝟙 Δ[0]) ≫
      (standardAlternatingExtensionCocone e T).val = c.val := by
  rw [← Category.comp_id (𝟙 (Δ[0] : SSet.{u})), joinMap_comp, Category.assoc,
    standardAlternatingExtensionCocone_join]
  exact splitCoconeExtension_old_val T

/-- 概要：次段の偶数前置図式は新しい表示余錐の偶数制限そのもの。
方針：偶数面の join 式と辺の終点の uncurry を合成する。
規約：全偶数前置単体を同時に比較する。
使われ方：元の filtered 表示図式の後続段との整合。 -/
lemma standardAlternatingExtension_even :
    (joinStdSimplexIso n 0).hom ≫ SSet.stdSimplex.map (sequentialEvenFace (n + 1)) ≫
      standardAlternatingExtension e =
      joinMap (SSet.stdSimplex.map (sequentialEvenFace n)) (𝟙 Δ[0]) ≫ d.val := by
  rw [← Category.assoc, sequentialEvenFace_successor_join, Category.assoc,
    standardAlternatingExtension_join]
  rw [← Category.id_comp (SSet.stdSimplex.δ (0 : Fin 2)),
    ← Category.comp_id (SSet.stdSimplex.map (sequentialEvenFace n)), joinMap_comp,
    Category.assoc, ← sliceUnderUncurry_precomp, e.δ_zero_yonedaEquiv_symm]
  rw [sliceUnderUncurry_yoneda, Category.comp_id]

end SerrePositivity.InfinityCategories.F2.Presentable
