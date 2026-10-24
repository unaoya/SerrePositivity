module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFamilyCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.TrivialFibrationIsoFaithful
public import SerrePositivity.InfinityCategories.HomotopyLimits.ArrowLeftIdentityCancellation
public import SerrePositivity.InfinityCategories.HomotopyLimits.FunctorHomSquareRealization
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyEndpointTransport

/-!
概要：動く終端を持つ同じ辺族間円柱に対し、元の切断比較円柱の自然性正方形を構成する。
方針：終端へ写した二つの積の恒等因子を消し、自明 Kan 制限の h Fun 上の忠実性で戻す。
規約：族間円柱・終端の切断像・両切断比較の四辺を保持。終端固定を追加仮定しない。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X T : SSet.{u}} [Quasicategory X] (e : (Δ[1] : SSet.{u}) ⟶ X)
  (y : X _⦋0⦌) {F G : T ⟶ coconeMappingSpace e y} (H : SSet.Homotopy F G)
local notation "r" => cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y
local notation "s" => cosliceEdgeSectionFiber e y
local notation "CF" => CosliceEdgeFamilyCylinder.homotopy (cosliceEdgeFamilyCylinder e y F)
local notation "CG" => CosliceEdgeFamilyCylinder.homotopy (cosliceEdgeFamilyCylinder e y G)

/-- 元の族間円柱の終端を同じ切断で戻し、両切断比較と同じ型付き端点へ揃える。 -/
def cosliceEdgeFamilySectionHomotopy : SSet.Homotopy ((F ≫ r) ≫ s) ((G ≫ r) ≫ s) :=
  homotopyEndpointTransport (functorHomotopyPostcomp H (r ≫ s))
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

/-- 終端の切断像も、元の同じ族間円柱の raw な像を保持する。 -/
lemma cosliceEdgeFamilySectionHomotopy_raw :
    (cosliceEdgeFamilySectionHomotopy e y H).h = H.h ≫ (r ≫ s) :=
  homotopyEndpointTransport_raw _ _ _

/-- 動く終端を同じ切断で戻す二経路は、元の指定した四円柱の同じ合成の類を持つ。 -/
lemma cosliceEdgeFamilyNaturality_homMk_comp :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy CF) ≫
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
          (cosliceEdgeFamilySectionHomotopy e y H)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) ≫
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy CG) := by
  let J := cosliceEdgeFamilySectionHomotopy e y H
  let I₀ := functorIsoOfSimplicialHomotopy CF
  let I₁ := functorIsoOfSimplicialHomotopy J
  let I₂ := functorIsoOfSimplicialHomotopy H
  let I₃ := functorIsoOfSimplicialHomotopy CG
  let P := (hoFunctor.map ((ihom T).map r)).toFunctor
  have := cosliceTriangleTarget_trivialKanFibration e y
  have h₀ := homotopyIso_postcomp_constant_arrow CF r (F ≫ r)
    (by simpa only [Category.assoc] using (cosliceEdgeFamilyCylinder e y F).target)
  have h₃ := homotopyIso_postcomp_constant_arrow CG r (G ≫ r)
    (by simpa only [Category.assoc] using (cosliceEdgeFamilyCylinder e y G).target)
  rw [functorIso_postcomp_hom] at h₀ h₃
  have hj := SerrePositivity.InfinityCategories.functorHomotopy_hom_arrow_of_h_eq
    (functorHomotopyPostcomp J r) (functorHomotopyPostcomp H r) (by
      change J.h ≫ r = H.h ≫ r
      dsimp only [J]
      rw [cosliceEdgeFamilySectionHomotopy_raw]
      simp only [Category.assoc, cosliceEdgeSectionFiber_target]
      exact congrArg (H.h ≫ ·) (Category.comp_id r))
  rw [functorHomotopyPostcomp_hom, functorHomotopyPostcomp_hom] at hj
  have hL := arrowLeftIdentity_cancel (P.map I₀.hom) (P.map I₁.hom)
    (P.map (I₀ ≪≫ I₁).hom) (P.map_comp _ _).symm h₀
  have hR := arrowRightIdentity_cancel (P.map I₂.hom) (P.map I₃.hom)
    (P.map (I₂ ≪≫ I₃).hom) (P.map_comp _ _).symm h₃
  apply trivialKanFibration_postcomp_iso_hom_injective r (I₀ ≪≫ I₁) (I₂ ≪≫ I₃)
  rw [functorIso_postcomp_hom, functorIso_postcomp_hom]
  exact hL.symm.trans (hj.trans hR)

/-- 同じ二つの切断比較と元の族間円柱・終端の切断像を四辺に保つ実際の正方形。 -/
def cosliceEdgeFamilyNaturalitySquare :
    SerrePositivity.InfinityCategories.FunctorHomSquare CF CG H (cosliceEdgeFamilySectionHomotopy e y H) :=
  (nonempty_functorHomSquare_of_homEq CF CG H (cosliceEdgeFamilySectionHomotopy e y H)
    (cosliceEdgeFamilyNaturality_homMk_comp e y H)).some

end
end SerrePositivity.InfinityCategories.HomotopyLimits
