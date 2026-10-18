module

public import SerrePositivity.KST.DerivedBlowup.DiagramModuleUnitCoherence
public import SerrePositivity.DifferentialGraded.Module.Left
public import SerrePositivity.DifferentialGraded.Category.Examples

/-!
概要：KST §3.1 の図式加群の指定単位矢に沿う underlying 複体図式。
方針：係数圏の単位関手と加群の共変 dg 関手を閉零射で合成する。
規約：基底環上の図式は得られるが、この矢の擬同型を cartesian 条件には使わない。
使われ方：指定の加群比較の恒等・三重整合性の underlying 計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：図式 dg 加群から指定単位矢に沿う通常の複体図式を取り出す。
方針：二重 opposite 比較で共変加群へ戻し、閉零射の通常複体を取る。
規約：KST §3.1、加群は依然として係数圏全体の dg 加群である。
使われ方：指定遷移の任意の包含鎖での合成を計算する。 -/
def diagramModuleUnderlyingDiagram
    (M : RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ) : J ⥤ Complex R :=
  diagramModuleUnitFunctor F ⋙ (LeftModule.ofRightOpposite M).onClosed ⋙ closedToComplex R

/-- 概要：underlying 図式の値は元の dg 加群の当該係数対象での複体。
方針：関手合成と二重 opposite の対象写像を展開する。
規約：KST §3.1。使われ方：局所評価との比較。 -/
theorem diagramModuleUnderlyingDiagram_obj
    (M : RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ) (i : J) :
    (diagramModuleUnderlyingDiagram F M).obj i = M.obj (op (op ⟨i⟩)) := rfl

/-- 概要：underlying 遷移は指定単位矢の dg 加群作用に一致する。
方針：閉零射の写像と二重 opposite 比較の恒等 Hom を展開する。
規約：KST §3.1。使われ方：canonical な局所加群比較の成分との同定。 -/
theorem diagramModuleUnderlyingDiagram_map
    (M : RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ) {i j : J} (h : i ≤ j) :
    (diagramModuleUnderlyingDiagram F M).map (homOfLE h) =
      mapFromUnit R _ _ (diagramModuleTransitionUnit F h ≫
        M.map (op (op ⟨i⟩)) (op (op ⟨j⟩))) := by
  change mapFromUnit R _ _ (diagramModuleTransitionUnit F h ≫
    (𝟙 _ ≫ M.map (op (op ⟨i⟩)) (op (op ⟨j⟩)))) = _
  rw [Category.id_comp]

/-- 概要：指定加群遷移の恒等包含に沿う写像は恒等。
方針：構成済みの実際の underlying 関手の恒等保存を使う。
規約：KST §3.1。使われ方：cartesian 比較の単位計算の基礎。 -/
theorem diagramModuleUnderlyingDiagram_id
    (M : RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ) (i : J) :
    (diagramModuleUnderlyingDiagram F M).map (homOfLE (le_refl i)) = 𝟙 _ :=
  (diagramModuleUnderlyingDiagram F M).map_id i

/-- 概要：指定加群遷移は三つの重なりの包含で合成と整合する。
方針：構成済みの実際の underlying 関手の合成保存を使う。
規約：KST §3.1、係数拡大後の随伴比較との整合性は別途示す。
使われ方：図式加群の全包含鎖に沿う指定作用の検算。 -/
theorem diagramModuleUnderlyingDiagram_comp
    (M : RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ)
    {i j k : J} (h : i ≤ j) (g : j ≤ k) :
    (diagramModuleUnderlyingDiagram F M).map (homOfLE (h.trans g)) =
      (diagramModuleUnderlyingDiagram F M).map (homOfLE h) ≫
        (diagramModuleUnderlyingDiagram F M).map (homOfLE g) :=
  (diagramModuleUnderlyingDiagram F M).map_comp (homOfLE h) (homOfLE g)

end SerrePositivity.KST.DerivedBlowup
