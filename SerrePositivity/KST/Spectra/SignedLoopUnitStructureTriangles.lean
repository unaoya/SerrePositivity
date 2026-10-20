module

public import SerrePositivity.KST.Spectra.SignedLoopUnitStructurePath
public import SerrePositivity.KST.Spectra.SignedLoopStructureTriangleFaces

/-!
概要：単位に実際に使う構造区間と、元の二辺の合成・逆向きの二つの三角形の照合。
方針：同じ Kan 列の保存済み二単体を公開し、単位の実辺へ厳密に同定する。
規約：旧区間との同じ辺の一致は仮定しない。使われ方：単位構造入力の高次比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
variable (X : OmegaSpectrum.{u})

/-- 実際の単位構造区間に使った、元の交換符号・二重反転の同じ合成三角形。 -/
def signedLoopUnitStructureCompositeTriangle (n : ℕ) :=
  KanSequence.signedLoopStructureCompositeTriangle X.toKanSequence X.toKanSequence_omega n

/-- 同じ単位構造区間と合成辺・定数辺を保持する、実際の逆向き三角形。 -/
def signedLoopUnitStructureInverseTriangle (n : ℕ) :=
  KanSequence.signedLoopStructureInverseTriangle X.toKanSequence X.toKanSequence_omega n

/-- 第一辺は元の交換符号の同じ評価区間。 -/
lemma signedLoopUnitStructureCompositeTriangle_two (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ signedLoopUnitStructureCompositeTriangle X n =
      (KanSequence.signedLoopStructureFirstInterval
        X.toKanSequence X.toKanSequence_omega n).path :=
  KanSequence.signedLoopStructureCompositeTriangle_two
    X.toKanSequence X.toKanSequence_omega n

/-- 第二辺は同じ自然な二重反転の評価区間。 -/
lemma signedLoopUnitStructureCompositeTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ signedLoopUnitStructureCompositeTriangle X n =
      (KanSequence.signedLoopStructureSecondInterval X.toKanSequence n).path :=
  KanSequence.signedLoopStructureCompositeTriangle_zero
    X.toKanSequence X.toKanSequence_omega n

/-- 同じ合成三角形の対角辺と逆向き三角形の第一辺は厳密に同じ実辺。 -/
lemma signedLoopUnitStructureTriangles_shared (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ signedLoopUnitStructureCompositeTriangle X n =
      stdSimplex.δ (2 : Fin 3) ≫ signedLoopUnitStructureInverseTriangle X n :=
  (KanSequence.signedLoopStructureCompositeTriangle_one
    X.toKanSequence X.toKanSequence_omega n).trans
      (KanSequence.signedLoopStructureInverseTriangle_two
        X.toKanSequence X.toKanSequence_omega n).symm

/-- 逆向き三角形の第二辺は、単位・全 Hom の共通入力に実際に使う構造辺そのもの。 -/
lemma signedLoopUnitStructureInverseTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ signedLoopUnitStructureInverseTriangle X n =
      (signedLoopUnitStructurePath X n).path :=
  KanSequence.signedLoopStructureInverseTriangle_zero
    X.toKanSequence X.toKanSequence_omega n

/-- 逆向き三角形の対角辺は、同じ元の構造像の頂点の評価像で一定。 -/
lemma signedLoopUnitStructureInverseTriangle_one (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ signedLoopUnitStructureInverseTriangle X n =
      SSet.const ((PointedMapping.uncurryAction (X.level n).space
        ((KanSequence.signedLoopTail X.toKanSequence).level (n + 1)).space).right.app _
          (PointedMapping.familyVertex (SignedAdjointPaths.left
            (KanSequence.kanAdjoint X.toKanSequence n)
            (KanSequence.kanAdjoint X.toKanSequence (n + 1))))) :=
  KanSequence.signedLoopStructureInverseTriangle_one
    X.toKanSequence X.toKanSequence_omega n

end SerrePositivity.KST.Spectra.OmegaSpectrum
