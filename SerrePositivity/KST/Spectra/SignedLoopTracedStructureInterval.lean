module

public import SerrePositivity.KST.Spectra.SignedLoopStructureCoordinates
public import SerrePositivity.KST.Spectra.SignedAdjointCompositionTriangles
public import SerrePositivity.KST.Spectra.PointedBasedPathUncurry

/-!
概要：元の二つの符号比較区間と実三角形を保持した、Kan 随伴の構造区間。
方針：保存した合成辺を同じ定数辺との三角形で逆向きにし、元の評価で uncurry する。
規約：成分からの区間の再選択なし。使われ方：単位と全 Hom に共通の構造入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.KanSequence
variable (X : KanSequence.{u}) (hX : X.OmegaCondition)

/-- 元の交換符号辺と同じ自然な二重反転辺を保持する、構造比較の合成三角形。 -/
def signedLoopStructureComposite (n : ℕ) :=
  SignedAdjointPaths.forwardComposite
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma (n + 2))) (hX (n + 2))
    (kanAdjoint X n) (kanAdjoint X (n + 1))

/-- 同じ合成辺と定数辺を持つ、逆向き構造比較の実三角形。 -/
def signedLoopStructureReverse (n : ℕ) :=
  SignedAdjointPaths.reverseComposite
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma (n + 2))) (hX (n + 2))
    (kanAdjoint X n) (kanAdjoint X (n + 1))

/-- 保存した元の実区間と二つの三角形から得る、実際の単位構造区間。 -/
def signedLoopStructureInterval (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint ((signedLoopTail X).level (n + 1)).space)
      (X.sigma n ≫ kanAdjoint X (n + 1))
      (PointedSimplicialSet.circle.{u} ◁ kanAdjoint X n ≫ (signedLoopTail X).sigma n) := by
  have hr := congrArg uncurry (signedAdjoint_structure_right X n)
  have hl := congrArg uncurry (signedAdjoint_structure_left X n)
  rw [uncurry_curry] at hr hl
  exact (signedLoopStructureReverse X hX n).path.basedUncurry.changeEndpoints hr hl

/-- 端点を元の構造射へ戻しても、保存した逆向き区間の同じ uncurry 像。 -/
lemma signedLoopStructureInterval_path (n : ℕ) :
    (signedLoopStructureInterval X hX n).path =
      (signedLoopStructureReverse X hX n).path.path ≫
        (PointedMapping.uncurryAction (X.level n).space
          ((signedLoopTail X).level (n + 1)).space).right := by
  exact (signedLoopStructureReverse X hX n).path.basedUncurry_path

/-- 元の二辺を持つ同じ合成三角形を、元の構造 Hom へ移した実二単体。 -/
def signedLoopStructureCompositeTriangle (n : ℕ) :=
  SSet.yonedaEquiv.symm (signedLoopStructureComposite X hX n).triangle.simplex ≫
    (PointedMapping.uncurryAction (X.level n).space
      ((signedLoopTail X).level (n + 1)).space).right

/-- 保存した逆向き三角形も、元の構造 Hom へ同じ評価で移す。 -/
def signedLoopStructureInverseTriangle (n : ℕ) :=
  SSet.yonedaEquiv.symm (signedLoopStructureReverse X hX n).triangle.simplex ≫
    (PointedMapping.uncurryAction (X.level n).space
      ((signedLoopTail X).level (n + 1)).space).right

/-- 逆向き三角形の第二辺は、単位へ使う同じ構造区間そのもの。 -/
lemma signedLoopStructureInverseTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ signedLoopStructureInverseTriangle X hX n =
      (signedLoopStructureInterval X hX n).path := by
  rw [signedLoopStructureInverseTriangle, ← Category.assoc,
    PointedMapping.BasedPathDifference.triangle_zero, signedLoopStructureInterval_path]

/-- 逆向き三角形の第一辺は、元の二辺を合成した同じ区間の評価像。 -/
lemma signedLoopStructureInverseTriangle_two (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ signedLoopStructureInverseTriangle X hX n =
      (signedLoopStructureComposite X hX n).path.basedUncurry.path := by
  rw [signedLoopStructureInverseTriangle, ← Category.assoc,
    PointedMapping.BasedPathDifference.triangle_two,
    PointedMapping.VerticalPath.basedUncurry_path]
  rfl

/-- 逆向き三角形の対角辺は、元の構造像の同じ頂点の評価像で一定。 -/
lemma signedLoopStructureInverseTriangle_one (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ signedLoopStructureInverseTriangle X hX n =
      SSet.const ((PointedMapping.uncurryAction (X.level n).space
        ((signedLoopTail X).level (n + 1)).space).right.app _
          (PointedMapping.familyVertex
            (SignedAdjointPaths.left (kanAdjoint X n) (kanAdjoint X (n + 1))))) := by
  rw [signedLoopStructureInverseTriangle, ← Category.assoc,
    PointedMapping.BasedPathDifference.triangle_one]
  change SSet.const _ ≫ _ = _
  rw [SSet.const_comp]
  rfl

end SerrePositivity.KST.Spectra.KanSequence
