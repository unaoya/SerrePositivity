module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightPrefixTriangleExtension
public import SerrePositivity.InfinityCategories.HomotopyLimits.RootedHomRootCoordinates

/-!
概要：同じ右四面体の δ₁ 面で、右初面の長辺と修正後の共通長辺を接続する。
方針：元の三面・修正辺・底の退化を単体恒等式で回収する。
規約：修正辺を選び直さない。使われ方：共通長辺空間内の修正を含む右比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 修正面の初辺 02 は、右初面の長辺 02 と同じ形状。 -/
lemma tetrahedronCorrection_first_shape :
    (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4) :
      (Δ[1] : SSet.{u}) ⟶ Δ[3]) =
      stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 修正面の終端辺は、元の終端面の修正辺 23 と同じ形状。 -/
lemma tetrahedronCorrection_last_shape :
    (stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4) :
      (Δ[1] : SSet.{u}) ⟶ Δ[3]) =
      stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 修正面の底は、元の右二単体の長辺の右退化。 -/
lemma tetrahedronCorrection_base_shape :
    (stdSimplex.δ (1 : Fin 4) ≫ stdSimplex.σ (2 : Fin 3) :
      (Δ[2] : SSet.{u}) ⟶ Δ[2]) =
      stdSimplex.σ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "T" => specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "r" => normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p)
local notation "P" => specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC
local notation "κ" => partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC

/-- 元の右四面体の δ₁ 面。初面の長辺に同じ修正辺を後置する実際の三角形。 -/
def specifiedCoconeRightCorrectionFace :
    (Δ[2] : SSet.{u + 1}) ⟶ sliceUnder (f ≫ (i ≫ p)) :=
  stdSimplex.δ (1 : Fin 4) ≫ T

/-- 初辺は右初面の同じ長辺である。 -/
lemma specifiedCoconeRightCorrectionFace_first :
    stdSimplex.δ (2 : Fin 3) ≫ specifiedCoconeRightCorrectionFace hp p c hc dB dC =
      stdSimplex.δ (1 : Fin 3) ≫ P :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ T) tetrahedronCorrection_first_shape).trans (Category.assoc _ _ _))

/-- 終端辺は元の指定修正辺を共通部分へ制限したもの。 -/
lemma specifiedCoconeRightCorrectionFace_second :
    stdSimplex.δ (0 : Fin 3) ≫ specifiedCoconeRightCorrectionFace hp p c hc dB dC =
      SSet.yonedaEquiv.symm (κ).edge ≫ r := by
  have hterminal : stdSimplex.δ (0 : Fin 3) ≫
      (stdSimplex.δ (0 : Fin 4) ≫ T) = SSet.yonedaEquiv.symm (κ).edge ≫ r :=
    (congrArg (fun z ↦ stdSimplex.δ (0 : Fin 3) ≫ z)
      (specifiedCoconeRootedRightTetrahedron_terminalFace hp p c hc dB dC)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z ↦ z ≫ r) (specifiedCoconeRightTriangle_correction hp p c hc dB dC)))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ T) tetrahedronCorrection_last_shape).trans
      ((Category.assoc _ _ _).trans hterminal))

/-- 長辺は修正後の同じ四面体の共通長辺 03 そのもの。 -/
lemma specifiedCoconeRightCorrectionFace_long :
    stdSimplex.δ (1 : Fin 3) ≫ specifiedCoconeRightCorrectionFace hp p c hc dB dC =
      tetrahedronRootEdge ≫ T := (Category.assoc _ _ _).symm

/-- 右初面の長辺も、同じ native な共通長辺を一単体として被覆する。 -/
lemma specifiedCoconeRightPrefixRootedTriangle_rootProjection :
    (stdSimplex.δ (1 : Fin 3) ≫ P) ≫ q =
      specifiedCoconeNativeRootEdge hp p c hc dB dC := by
  have hb : stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm
      (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).simplex =
      specifiedCoconeNativeRootEdge hp p c hc dB dC := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm
      (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).d₁
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ stdSimplex.δ (1 : Fin 3) ≫ z)
      (specifiedCoconeRightPrefixRootedTriangle_projection hp p c hc dB dC)).trans hb)

/-- 修正面の底は、同じ native な共通長辺の右退化である。 -/
lemma specifiedCoconeRightCorrectionFace_projection :
    specifiedCoconeRightCorrectionFace hp p c hc dB dC ≫ q =
      stdSimplex.σ (1 : Fin 2) ≫ specifiedCoconeNativeRootEdge hp p c hc dB dC := by
  let β := SSet.yonedaEquiv.symm (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).simplex
  have hb : stdSimplex.δ (1 : Fin 3) ≫ β =
      specifiedCoconeNativeRootEdge hp p c hc dB dC := by
    dsimp only [β]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm
      (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).d₁
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ stdSimplex.δ (1 : Fin 4) ≫ z)
      (specifiedCoconeRootedRightTetrahedron_base hp p c hc dB dC)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z ↦ z ≫ β) tetrahedronCorrection_base_shape).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun z ↦ stdSimplex.σ (1 : Fin 2) ≫ z) hb)))))

/-- 修正面の始点は同じ元の共通余錐に固定される。 -/
lemma specifiedCoconeRightCorrectionFace_initial :
    (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ≫
        specifiedCoconeRightCorrectionFace hp p c hc dB dC = SSet.yonedaEquiv.symm c :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ stdSimplex.δ (1 : Fin 2) ≫ z)
      (specifiedCoconeRightCorrectionFace_first hp p c hc dB dC)).trans
        ((Category.assoc _ _ _).symm.trans
          (specifiedCoconeRightPrefixTriangleExtension_initial hp p c hc dB dC)))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
