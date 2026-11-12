module

public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection

/-!
# 同じ単体的ホモトピーで結ばれる射の弱同値性の移送

概要：実際にホモトピックな二射は同時に弱ホモトピー同値となる。
方針：anodyne を反転する Kan 標的の元の反変 π₀ に同じホモトピーを送る。
規約：元の二射の始域・終域の充填性を要求しない。
使われ方：相対自然変換の前後合成の比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

lemma homotopy_weak_iff {A B : SSet.{u}} {f g : A ⟶ B} (H : SSet.Homotopy f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence g := by
  have he (Z : SSet.{u}) [SSet.KanComplex Z] :
      (FrameHom.AnodyneWeakDetection.homComponents Z).map f.op =
        (FrameHom.AnodyneWeakDetection.homComponents Z).map g.op := by
    have h := AnodyneHomotopy.map_homotopy_eq
      (FrameHom.AnodyneWeakDetection.homComponents Z).rightOp
      (FrameHom.AnodyneWeakDetection.homComponents_inverts Z) H
    exact congrArg Quiver.Hom.unop h
  constructor
  · intro hf Z hZ
    change Function.Bijective ((FrameHom.AnodyneWeakDetection.homComponents Z).map g.op)
    rw [← he Z]
    exact hf Z
  · intro hg Z hZ
    change Function.Bijective ((FrameHom.AnodyneWeakDetection.homComponents Z).map f.op)
    rw [he Z]
    exact hg Z

end SerrePositivity.EInfinity.Hammock
