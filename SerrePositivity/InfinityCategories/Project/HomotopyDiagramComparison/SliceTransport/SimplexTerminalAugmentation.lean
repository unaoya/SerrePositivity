module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.SimplexTerminalParameter
public import Mathlib.CategoryTheory.Elements

/-!
# 反対要素圏の nerve の元の単体集合への終端 augmentation

概要：共通比較の始域の nerve から元の単体集合への実際の自然な射を構成する。
方針：列の最後の単体に全頂点を表示し、終端の尾を含む reindexing の式を使う。
規約：全ての面・退化と元の単体集合の係数射に自然。
使われ方：Dwyer–Kan §7 の frame 側の共通比較の左射。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalAugmentation

open CategoryTheory Opposite

variable (K : SSet.{v})

/-- 概要：反対要素圏の列の同じ終端パラメータ（Dwyer–Kan §7）。
方針：要素を忘れた単体作用素の列の終端頂点写像を使う。
規約：元の列の全作用素を保持する。
使われ方：終端単体から元の単体を取り出す。 -/
abbrev parameter {n : ℕ} (c : ComposableArrows K.Elementsᵒᵖ n) :
    SimplexCategory.mk n ⟶ (c.obj (Fin.last n)).unop.obj.unop :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalParameter.parameter (c ⋙ (Functor.Elements.π K).leftOp)

/-- 概要：反対要素圏の元の射列を元の単体集合の同じ単体へ送る（Dwyer–Kan §7）。
方針：終端単体を元の終端パラメータで制限する。
規約：全頂点を同じ終端単体の中で扱う。
使われ方：終端 augmentation の成分。 -/
abbrev simplex {n : ℕ} (c : ComposableArrows K.Elementsᵒᵖ n) :
    K.obj (op (SimplexCategory.mk n)) :=
  K.map (parameter K c).op (c.obj (Fin.last n)).unop.val

/-- 概要：終端単体からの制限は全単体作用素と可換（Dwyer–Kan §7）。
方針：新しい終端から元の終端への尾と要素圏の整合式を使う。
規約：最終頂点を変える作用素も省略しない。
使われ方：終端 augmentation の全自然性。 -/
lemma simplex_operator {n m : ℕ} (c : ComposableArrows K.Elementsᵒᵖ n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    K.map θ.op (simplex K c) =
      simplex K ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
  let d := (SimplexCategory.toCat.map θ).toFunctor ⋙ c
  let k := c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))
  change K.map θ.op (K.map (parameter K c).op (c.obj (Fin.last n)).unop.val) =
    K.map (parameter K d).op (c.obj (θ.toOrderHom (Fin.last m))).unop.val
  calc
    _ = K.map (θ ≫ parameter K c).op (c.obj (Fin.last n)).unop.val :=
      (congrArg (fun f => f (c.obj (Fin.last n)).unop.val)
        (K.map_comp (parameter K c).op θ.op)).symm
    _ = K.map (parameter K d).op (K.map k.unop.hom (c.obj (Fin.last n)).unop.val) := by
      rw [show θ ≫ parameter K c = parameter K d ≫ k.unop.hom.unop from
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalParameter.reindex (c ⋙ (Functor.Elements.π K).leftOp) θ]
      exact congrArg (fun f => f (c.obj (Fin.last n)).unop.val)
        (K.map_comp k.unop.hom (parameter K d).op)
    _ = _ := congrArg (fun x => K.map (parameter K d).op x) k.unop.map_val

/-- 概要：反対要素圏の nerve から元の単体集合への実際の射（Dwyer–Kan §7）。
方針：元の終端単体の制限と全作用素の整合を束ねる。
規約：元の単体集合や nerve を置き換えない。
使われ方：共通比較の左側の元の射。 -/
def augmentation : nerve K.Elementsᵒᵖ ⟶ K where
  app _ := ↾fun c => simplex K c
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro c
    exact (simplex_operator K c θ.unop).symm

/-- 概要：元の零単体の要素の頂点は同じ零単体へ戻る（Dwyer–Kan §7）。
方針：零次の終端パラメータが恒等であることを使う。
規約：元の零単体を変更しない。
使われ方：共通比較の同じ射の零次の正規化。 -/
lemma augmentation_zero (x : K.obj (op (SimplexCategory.mk 0))) :
    (augmentation K).app (op (SimplexCategory.mk 0))
        (ComposableArrows.mk₀ (op (K.elementsMk (op (SimplexCategory.mk 0)) x))) = x := by
  have h : parameter K
      (ComposableArrows.mk₀ (op (K.elementsMk (op (SimplexCategory.mk 0)) x))) =
        𝟙 (SimplexCategory.mk 0) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    change (_ : Fin 1) = _
    exact Subsingleton.elim _ _
  change K.map (parameter K
    (ComposableArrows.mk₀ (op (K.elementsMk (op (SimplexCategory.mk 0)) x)))).op x = x
  rw [h]
  exact ConcreteCategory.congr_hom (K.map_id (op (SimplexCategory.mk 0))) x

/-- 概要：同じ終端 augmentation は単体集合の係数射にも自然（Dwyer–Kan §7）。
方針：元の単体写像の自然性を同じ終端パラメータに適用する。
規約：全単体と全係数射を保持する。
使われ方：全体の自然変換と反転性の帰納。 -/
lemma naturality {L : SSet.{v}} (f : K ⟶ L) :
    nerveMap f.mapElements.op ≫ augmentation L = augmentation K ≫ f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  exact (congrArg (fun k => k (c.obj (Fin.last n.unop.len)).unop.val)
    (f.naturality (parameter K c).op)).symm

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalAugmentation
