module

public import SerrePositivity.EInfinity.Hammock.ColimitCompositionPoints
public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorTarget
public import SerrePositivity.EInfinity.Hammock.AllMarkedNative

/-!
# 同じ指定 prefix・生成矢・残りからの元の hammock への貼り戻し

概要：元の三因子を既存の hammock 合成で接続する単体写像を構成する。
方針：指定部分圏の元の包含と同じ生成射の一定単体を使う。
規約：実際の二つの余極限の点と元の生成矢を保持する。
使われ方：反復切断の貼り戻しと抽出との両逆。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FactorTarget
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X Y : Paths C)
  {n m : SimplexCategoryᵒᵖ}

def pastePoint (g : Index W) (p : (left W X g.val).obj n) (r : (right W Y g.val).obj n) :
    (colimitGraph W.paths X Y).obj n :=
  composePoint W.paths X g.val.right Y
    (composePoint W.paths X g.val.left g.val.right ((AllMarked.inclusion W X g.val.left).app n p)
      (arrowPoint W.paths g.val.hom.toPath n)) r

lemma pastePoint_simplex (θ : n ⟶ m) (g : Index W) (p : (left W X g.val).obj n)
    (r : (right W Y g.val).obj n) :
    pastePoint W X Y g ((left W X g.val).map θ p) ((right W Y g.val).map θ r) =
      (colimitGraph W.paths X Y).map θ (pastePoint W X Y g p r) := by
  have hp := congrArg (fun k => k p) ((AllMarked.inclusion W X g.val.left).naturality θ)
  have hi := (congrArg₂ (composePoint W.paths X g.val.left g.val.right) hp
    (arrowPoint_simplex W.paths θ g.val.hom.toPath).symm).trans
      (composePoint_simplex W.paths X g.val.left g.val.right θ
        ((AllMarked.inclusion W X g.val.left).app n p) (arrowPoint W.paths g.val.hom.toPath n))
  exact (congrArg₂ (composePoint W.paths X g.val.right Y) hi rfl).trans
    (composePoint_simplex W.paths X g.val.right Y θ
      (composePoint W.paths X g.val.left g.val.right ((AllMarked.inclusion W X g.val.left).app n p)
        (arrowPoint W.paths g.val.hom.toPath n)) r)

def paste : space W X Y ⟶ colimitGraph W.paths X Y where
  app _ := ↾fun s => pastePoint W X Y s.1 s.2.1 s.2.2
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro s
    exact pastePoint_simplex W X Y θ s.1 s.2.1 s.2.2

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FactorTarget
