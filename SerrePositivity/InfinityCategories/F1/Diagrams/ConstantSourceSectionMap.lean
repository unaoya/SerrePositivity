module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ConstantSourceRelativeEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionsFunctor

/-!
概要：定値始域からの底上の射を、同じ fiber から全切断への実際の射へ curry する。
方針：定値全空間の直積表示で評価し、元の底を固定して全切断へ持ち上げる。
規約：元の底上の射と指定頂点を保持する。
使われ方：全 Hom 作用の合成の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) (z : SpaceInfinity.{u} _⦋0⦌)
  (g : leftUnstraightening (SSet.const z : B ⟶ _) ⟶ leftUnstraightening F)
  (hg : g ≫ leftUnstraighteningProjection F =
    leftUnstraighteningProjection (SSet.const z : B ⟶ _))

/-- 同じ定値全空間からの底上の射を、元の fiber からの全切断の族にする。 -/
def constantSourceSectionMap :
    vertexFiber pointedSpaceProjection z ⟶
      HomotopyLimits.simplicialSections (leftUnstraighteningProjection F) :=
  HomotopyLimits.simplicialSectionsLift
    ((constantUnstraighteningSourceOverIso B z).inv.left ≫ g) (by
      rw [Category.assoc, hg]
      exact (constantUnstraighteningSourceOverIso B z).inv.w)

/-- 元の全切断の族の評価は、同じ底上の射の直積表示そのもの。 -/
lemma constantSourceSectionMap_evaluation :
    (B ◁ constantSourceSectionMap F z g hg) ≫
      HomotopyLimits.simplicialSectionsEvaluation (leftUnstraighteningProjection F) =
        (constantUnstraighteningSourceOverIso B z).inv.left ≫ g :=
  HomotopyLimits.simplicialSectionsLift_evaluation _ _

/-- 定値始域比較の頂点は、同じ底上の射から作る全切断の族の頂点と一致。 -/
lemma constantSourceSectionMap_vertex :
    (constantUnstraighteningSourceRelativeIso F z).hom.app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex (leftUnstraighteningProjection F)
        (leftUnstraighteningProjection (SSet.const z)) g hg) =
      functorVertex (constantSourceSectionMap F z g hg) := by
  let t := relativeFunctorVertex (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection (SSet.const z)) g hg
  let s := (functorVertexEquiv _ _).symm
    ((constantUnstraighteningSourceRelativeIso F z).hom.app (Opposite.op ⦋0⦌) t)
  have hs : functorVertex s =
      (constantUnstraighteningSourceRelativeIso F z).hom.app (Opposite.op ⦋0⦌) t :=
    (functorVertexEquiv _ _).apply_symm_apply _
  have h := constantUnstraighteningSourceRelativeIso_evaluation F z
    (SSet.const t : (Δ[0] : SSet.{u + 1}) ⟶ _)
  rw [SSet.const_comp, ← hs, uncurry_const_functorVertex] at h
  have he : relativeFunctorUncurry (SSet.const t : (Δ[0] : SSet.{u + 1}) ⟶ _) =
      fst (leftUnstraightening (SSet.const z : B ⟶ _)) Δ[0] ≫ g := by
    rw [relativeFunctorUncurry, SSet.const_comp]
    exact uncurry_const_functorVertex g
  rw [he] at h
  have hv : s = constantSourceSectionMap F z g hg := by
    apply HomotopyLimits.simplicialSections_hom_ext
    rw [constantSourceSectionMap_evaluation]
    have h' := congrArg (fun q ↦ (B ◁ (lift (𝟙 (vertexFiber pointedSpaceProjection z))
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))))) ≫ q) h
    change (B ◁ s) ≫
      HomotopyLimits.simplicialSectionsEvaluation (leftUnstraighteningProjection F) =
        (constantUnstraighteningSourceOverIso B z).inv.left ≫ g at h'
    exact h'
  exact hs.symm.trans (congrArg functorVertex hv)

end SerrePositivity.InfinityCategories
