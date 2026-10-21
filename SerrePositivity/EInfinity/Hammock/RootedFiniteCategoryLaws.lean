module

public import SerrePositivity.EInfinity.Hammock.RootedFiniteCategory

/-!
# 有限包の固定語の包含関手の厳密な恒等と合成

概要：元の有限部分集合の包含が元の固定端点の関手として厳密に整合する。
方針：元の自由関手の等式を既存の端点移送の整合へ渡す。
規約：元の両端と同じ全縦射を保持する。
使われ方：有限部分集合で添字付けた圏値・nerve 図式。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RootedFinite
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q)

lemma mapFunctor_id (a : Word) (S : Finset Q) :
    mapFunctor T X Y a (Finset.Subset.refl S) = 𝟭 (termCategory T X Y a S) := by
  let := FiniteQuiver.quiver (hull T X Y S)
  calc
    _ = Zigzag.Relative.fixedFunctor
        (LocalizerMorphism.id (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex (hull T X Y S)))))
        (rfl : left T X Y S = left T X Y S) (rfl : right T X Y S = right T X Y S) :=
      Zigzag.Relative.fixedFunctor_congr
        (F := FiniteQuiver.subsetRelative
          (QuiverTree.endpointHull_mono T X Y (Finset.Subset.refl S)))
        (G := LocalizerMorphism.id _) (w := a)
        (FiniteQuiver.subsetFunctor_refl (hull T X Y S)) rfl rfl rfl rfl
    _ = _ := Zigzag.Relative.fixedFunctor_id _ _

lemma mapFunctor_comp (a : Word) {S R U : Finset Q} (h : S ⊆ R) (k : R ⊆ U) :
    mapFunctor T X Y a (h.trans k) = mapFunctor T X Y a h ⋙ mapFunctor T X Y a k := by
  let := FiniteQuiver.quiver (hull T X Y S)
  let := FiniteQuiver.quiver (hull T X Y R)
  let := FiniteQuiver.quiver (hull T X Y U)
  let F := FiniteQuiver.subsetRelative (QuiverTree.endpointHull_mono T X Y h)
  let G := FiniteQuiver.subsetRelative (QuiverTree.endpointHull_mono T X Y k)
  calc
    _ = Zigzag.Relative.fixedFunctor (F.comp G)
        (rfl : (F.comp G).functor.obj (left T X Y S) = left T X Y U)
        (rfl : (F.comp G).functor.obj (right T X Y S) = right T X Y U) :=
      Zigzag.Relative.fixedFunctor_congr
        (F := FiniteQuiver.subsetRelative (QuiverTree.endpointHull_mono T X Y (h.trans k)))
        (G := F.comp G) (w := a)
        (FiniteQuiver.subsetFunctor_comp (QuiverTree.endpointHull_mono T X Y h)
          (QuiverTree.endpointHull_mono T X Y k)) rfl rfl rfl rfl
    _ = _ := Zigzag.Relative.fixedFunctor_comp F G rfl rfl rfl rfl

end SerrePositivity.EInfinity.Hammock.RootedFinite
