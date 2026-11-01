module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardContextDiagrams
public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardMovingExtractMapRecovery
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramPartRecovery

/-!
# 任意の前後の語の中の置換を元の恒等図式へ戻す

概要：全対象と全縦射の再構成を照合し、置換の比較を元の恒等図式へ接続する。
方針：局所ブロックの回収と二度の前後分割の回収を合成する。
規約：元の任意の前後の語、全体の固定端点、動く局所接合点を保持する。
使われ方：中央 backward 列の全部分圏への第一の包含の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Context
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : Word) (n m : ℕ) (X Y : C)

lemma rebuiltDiagram_eq : rebuiltDiagram a b n m X Y = originalDiagram a b n m X Y := by
  unfold rebuiltDiagram coreFamily
  rw [MovingExtract.rebuildDiagram_eq]
  change (((originalDiagram a b n m X Y).leftPart.leftPart).append
    (originalDiagram a b n m X Y).leftPart.rightPart).append
      (originalDiagram a b n m X Y).rightPart = _
  rw [Zigzag.MovingDiagram.append_parts, Zigzag.MovingDiagram.append_parts]

lemma rebuiltFunctor_eq : rebuiltFunctor a b n m X Y =
    𝟭 (Zigzag (weakEquivalences C) (wholeWord a b n m) X Y) := by
  unfold rebuiltFunctor
  rw [rebuiltDiagram_eq]
  rfl

variable (cof : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))

def pullbackOriginalCounit : pullbackFunctor a b n m X Y cof ⟶
    𝟭 (Zigzag (weakEquivalences C) (wholeWord a b n m) X Y) :=
  pullbackCounit a b n m X Y cof ≫ eqToHom (rebuiltFunctor_eq a b n m X Y)

variable (hc : ∀ S, trivialCofibrations C ((coreFamily a b n m X Y).middle.app S))

def pushoutOriginalUnit : 𝟭 (Zigzag (weakEquivalences C) (wholeWord a b n m) X Y) ⟶
    pushoutFunctor a b n m X Y hc :=
  eqToHom (rebuiltFunctor_eq a b n m X Y).symm ≫ pushoutUnit a b n m X Y hc

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Context
