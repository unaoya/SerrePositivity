module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedCutAttachments

/-!
# 内部の切断を前後の全語へ貼った prefix と残り

概要：指定接頭射と残りの射を一列の図式にし、元の前後の全語に接続する。
方針：接合点関手を共有して MovingDiagram.append を適用する。
規約：元の全縦射と両端の固定対象を保持する。
使われ方：指定 prefix の W-hammock への回収と全体の貼り戻し。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ [])

lemma eqToHom_mem {P Q : Paths C} (e : P = Q) : W.paths (eqToHom e) := by
  cases e
  exact W.paths.id_mem _

lemma leftAttachment_mem (k : Fin (n.unop.len + 1)) : W.paths ((leftAttachment W τ i h).app k) := by
  change W.paths ((eqToHom (sourceJoint_eq_rowSource W τ i h)).app k ≫ (rowPrefix W τ i h).app k)
  rw [eqToHom_app]
  exact W.paths.comp_mem _ _ (eqToHom_mem W _) (rowPrefix_mem W τ i h k)

def leftBlock := ForwardZigzag.diagram W.paths (leftAttachment W τ i h)
  (fun f => (beforeDiagram W τ i).endpoint_right_mem f) (fun _ => W.paths.id_mem _)

def rightBlock := ForwardZigzag.diagram W.paths (rightAttachment W τ i h)
  (fun _ => W.paths.id_mem _) (fun f => (afterDiagram W τ i).endpoint_left_mem f)

def generatorBlock := ForwardZigzag.diagram W.paths (rowGeneratorMap W τ i h)
  (fun _ => W.paths.id_mem _) (fun _ => W.paths.id_mem _)

def prefixDiagram := (beforeDiagram W τ i).append (leftBlock W τ i h)

def residualDiagram := (rightBlock W τ i h).append (afterDiagram W τ i)

def refinedDiagram :=
  ((prefixDiagram W τ i h).append (generatorBlock W τ i h)).append (residualDiagram W τ i h)

def refinedFunctor := (refinedDiagram W τ i h).fixedFunctor

def prefixFunctor := (prefixDiagram W τ i h).fixedFunctor

def residualFunctor := (residualDiagram W τ i h).fixedFunctor

lemma leftBlock_arrow_mem (k : Fin (n.unop.len + 1)) (j : Fin 1) :
    W.paths (((leftBlock W τ i h).obj k).arrow j) :=
  ForwardZigzag.diagram_arrow_mem W.paths (leftAttachment W τ i h)
    (fun f => (beforeDiagram W τ i).endpoint_right_mem f) (fun _ => W.paths.id_mem _)
    (leftAttachment_mem W τ i h) k j

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
