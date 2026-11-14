module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramConeClasses
public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitComparison
public import SerrePositivity.EInfinity.BarrattEccles.CarrierRightSimplicialCones
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.MixedFrameDiagrams

/-!
# 通常の錐の二つの族の混合 Hom 内での厳密な照合

概要：BM 命題 4.1・Hovey §5.4 の同じ通常の錐の両 frame の族を照合する。
方針：同じ反対射表示を元の添字へ戻し、二つの augmentation の結合則を使う。
規約：元の錐・試験始域・右 frame を保持する。
使われ方：具体的な両錐比較による元の錐の類の保存。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.Reedy
open SerrePositivity.DiagramModel
open SerrePositivity.EInfinity.FrameHom.MixedFrame

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：通常の錐の右族を元の添字上の同じ Hom 図式で表示（Hovey §5.4）。
方針：二重反対圏の族を戻し、同じ射の反対化同型の逆を合成する。
規約：既存の carrierStrictConeWeightedFamily と同じ族。
使われ方：混合 Hom の右比較へ入力する通常の錐。 -/
def carrierStrictSimplicialConeFamily (F : K ⥤ (operad A).Algebra) (c : Cone ((Diagram.forget A
  K).obj F)) :
    HomotopyWeight.weight K ⟶ carrierRightSimplicialHomDiagram A K c.pt F :=
  Functor.whiskerLeft (opOpEquivalence K).inverse
      (carrierStrictConeWeightedFamily A K F (HomotopyWeight.weight K) c ≫
        (FrameWeightRealization.hom Kᵒᵖ (carrierRightFrameDiagram A K F)).map
          ((carrierFramedLimitProbeComparison A).app c.pt).op) ≫
    Functor.whiskerLeft (opOpEquivalence K).inverse
      (carrierRightSimplicialHomDiagramIso A K c.pt F).inv

/-- 概要：右族の各単体は元の錐の脚と両比較の同じ合成（Hovey §5.4）。
方針：各次元で元の反対射を unop する。
規約：重みの単体に依存しない同じ式。
使われ方：始域族との混合 Hom 内での厳密な一致。 -/
lemma carrierStrictSimplicialConeFamily_app (F : K ⥤ (operad A).Algebra) (c : Cone
  ((Diagram.forget A K).obj F))
    (k : K) (n : SimplexCategoryᵒᵖ) (x : ((HomotopyWeight.weight K).obj k).obj n) :
    (((carrierStrictSimplicialConeFamily A K F c).app k).app n) x =
      (carrierFramedLimitProbeComparison A).app c.pt ≫ c.π.app k ≫ (rightFrameComparison A (F.obj
        k) n.unop).hom := rfl

/-- 概要：元の錐の両族は混合 Hom への比較で厳密に一致（Hovey §5.4）。
方針：始域族の全単体の式と右族の式を同じ結合則で照合する。
規約：両 augmentation と元の錐の脚を保持する。
使われ方：両錐比較が元の錐の類を保つことの根拠。 -/
lemma carrierStrictConeFamilies_mixed (F : K ⥤ (operad A).Algebra) (c : Cone ((Diagram.forget A
  K).obj F)) :
    let := projectiveModelCategory A
    let q := cosimplicialResolutionFamily (carrierProbeFactorization A)
    let P := carrierFramedLimitProbe A c.pt
    let f : (Functor.const K).obj P ⟶ (Diagram.forget A K).obj F :=
      (Functor.const K).map ((carrierFramedLimitProbeComparison A).app c.pt) ≫ c.π
    let R := F ⋙ carrierRightSimplicialFrameFamily A
    let b := Functor.whiskerLeft F (carrierRightSimplicialFrameAugmentation A)
    (CarrierDiagram.constantDiagramHomEquiv A K P ((Diagram.forget A K).obj F))
      ((CarrierDiagram.constantDiagramComparison A K).app P ≫ f) ≫
        _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison K (q.obj.obj P) ((Diagram.forget A K).obj F) R b =
      carrierStrictSimplicialConeFamily A K F c ≫
        _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison K (q.obj.obj P) (q.augmentation.app P) R := by
  let := projectiveModelCategory A
  let q := cosimplicialResolutionFamily (carrierProbeFactorization A)
  let P := carrierFramedLimitProbe A c.pt
  let f : (Functor.const K).obj P ⟶ (Diagram.forget A K).obj F :=
    (Functor.const K).map ((carrierFramedLimitProbeComparison A).app c.pt) ≫ c.π
  dsimp only
  ext k n x
  change ((((CarrierDiagram.constantDiagramHomEquiv A K P ((Diagram.forget A K).obj F))
      ((CarrierDiagram.constantDiagramComparison A K).app P ≫ f)).app k).app n) x ≫
        ((carrierRightSimplicialFrameAugmentation A).app (F.obj k)).app n =
    (q.augmentation.app P).app n.unop ≫ (((carrierStrictSimplicialConeFamily A K F c).app k).app
      n) x
  rw [CarrierDiagram.constantDiagramHomEquiv_comparison_app, carrierStrictSimplicialConeFamily_app]
  change ((q.augmentation.app P).app n.unop ≫
    ((carrierFramedLimitProbeComparison A).app c.pt ≫ c.π.app k)) ≫
      (rightFrameComparison A (F.obj k) n.unop).hom = _
  simp only [Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles
