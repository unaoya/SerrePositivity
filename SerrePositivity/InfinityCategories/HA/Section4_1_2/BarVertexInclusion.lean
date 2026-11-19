module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.NerveLoopMultiplication
public import SerrePositivity.KST.Comparison.GroupCompletion

/-!
# 零次モノイドの nerve から対角 bar への包含

概要：零次の元を全次数へ退化させて単体的モノイドとその bar に含める。
方針：各標準単体から零単体への一意な射を使う。
規約：KST Lemma 2.13 の基本群の積を具体的な射列で検査するための比較。
使われ方：有限 rank・安定 rank の一般線形群の基本群の代表。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：零次モノイドの定数図式から元の単体的モノイドへの自然な射。
方針：各単体から零単体への一意な射による退化を取る。
規約：この写像は全ての面・退化と可換する。
使われ方：零次モノイドの nerve の bar への射。
-/
def monoidVertexInclusion (M : SimplicialObject MonCat.{u}) :
    (Functor.const SimplexCategoryᵒᵖ).obj (M.obj (op ⦋0⦌)) ⟶ M where
  app n := M.map (SimplexCategory.const n.unop ⦋0⦌ 0).op
  naturality {m n} f := by
    change 𝟙 _ ≫ _ = _ ≫ M.map f
    rw [Category.id_comp, ← M.map_comp]
    congr 1

/--
概要：定数単体的モノイドの bar は一対象圏の nerve と同型。
方針：各次数で同じ射列を取り、恒等モノイド射の作用を確認する。
規約：対角模型と通常の nerve の一致。
使われ方：零次モノイドの辺と二単体を対角 bar へ移す。
-/
def constantMonoidBarIso (T : MonCat.{u}) :
    monoidBar ((Functor.const SimplexCategoryᵒᵖ).obj T) ≅ nerve (SingleObj T) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro m n f
    apply ConcreteCategory.hom_ext
    intro s
    apply ComposableArrows.ext (fun _ => rfl)
    intro i hi
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id])

/--
概要：零次モノイドの一対象圏の nerve から対角 bar への自然な射。
方針：定数モノイドの bar との同型と零次の退化の bar を合成する。
規約：辺の向きを保持する。
使われ方：分類空間の基本群における行列の元の代表。
-/
def monoidVertexNerveMap (M : SimplicialObject MonCat.{u}) :
    nerve (SingleObj (M.obj (op ⦋0⦌))) ⟶ monoidBar M :=
  (constantMonoidBarIso (M.obj (op ⦋0⦌))).inv ≫ monoidBarMap (monoidVertexInclusion M)

/--
概要：零次モノイドの nerve の基点は bar の標準基点へ送られる。
方針：零次の射列の唯一の対象を比較する。
規約：零単体の厳密な等式。
使われ方：Kan 置換した bar への基点保存。
-/
theorem monoidVertexNerveMap_point (M : SimplicialObject MonCat.{u}) :
    (monoidVertexNerveMap M).app (op ⦋0⦌) (monoidNervePoint (M.obj (op ⦋0⦌))) =
      monoidBarBasepoint M :=
  ComposableArrows.ext₀ rfl

/--
概要：零次モノイドの nerve の辺は標準 bar の辺の単体へ送られる。
方針：辺のラベルの退化と一対象圏の射列の自然性を確認する。
規約：区間の一次単体は恒等写像。
使われ方：標準群完備化写像の円の代表との一致。
-/
theorem monoidVertexNerveMap_edge (M : SimplicialObject MonCat.{u})
    (a : M.obj (op ⦋0⦌)) :
    (monoidVertexNerveMap M).app (op ⦋1⦌) (monoidEdgeSimplex (M.obj (op ⦋0⦌)) a) =
      monoidBarEdgeAt M 1 ((M.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op).hom a)
        (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) := by
  have hr : monoidBarEdgeAt M 1
      ((M.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op).hom a)
      (stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) =
        monoidEdgeSimplex (M.obj (op ⦋1⦌))
          ((M.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op).hom a) := by
    unfold monoidBarEdgeAt
    rw [Equiv.apply_symm_apply, CategoryTheory.Functor.map_id]
    exact Functor.id_comp _
  exact (monoidEdgeSimplex_map (M.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op) a).trans hr.symm

end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.1.2.4" (partial := component) "仮定：通常のモノイド T を定値単体モノイドとする（HA の通常モノイドの場合）。結論：bar が SingleObj T の nerve に同型で、その n 単体と n 個の T の元の列が全単射になる（分類空間の構成と Segal 写像の成分に一致）。任意の単体集合からのモノイド再構成は含まれない。"] _root_.SerrePositivity.KST.Comparison.constantMonoidBarIso
