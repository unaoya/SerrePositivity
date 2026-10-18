module
public import SerrePositivity.KST.SConstruction.StablePushoutFamilies
public import SerrePositivity.KST.SConstruction.CofiberPreservesPushout

/-! # 完全関手による関手的 pushout の比較
概要：pushout 図式の後合成と、選んだ pushout の族の自然な関手同型を構成する。
方針：全押し出しの保存を全部分複体に適用し、同じ span 上の持ち上げを比較する。
規約：切断の厳密な保存を入力にしない。使われ方：McCarthy 法の関手的 pushout の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：全押し出しを保つ射による pushout 図式の後合成。
方針：内部 Hom の後合成を押し出しの全部分複体へ持ち上げる。
規約：選択した pushout の厳密な保存は要求しない。使われ方：押し出しの族の入力の自然性。 -/
def pushoutDiagramsPostcomp {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesSConstructionData f) :
    pushoutDiagrams C ⟶ pushoutDiagrams D :=
  fullSubcomplexLift IsPushoutDiagramVertex
    ((fullSubcomplexOnVertices _ IsPushoutDiagramVertex).ι ≫ (ihom (Δ[1] ⊗ Δ[1])).map f) (by
      intro v
      let F := (functorVertexEquiv (Δ[1] ⊗ Δ[1]) C).symm v.val
      have hv : functorVertex F = v.val := (functorVertexEquiv _ C).apply_symm_apply _
      have hF : IsPushoutSquare F := fullSubcomplexOnVertices_vertex v
      change IsPushoutSquare ((functorVertexEquiv (Δ[1] ⊗ Δ[1]) D).symm
        (((ihom (Δ[1] ⊗ Δ[1])).map f).app (Opposite.op ⦋0⦌) v.val))
      rw [← hv]
      change IsPushoutSquare ((functorVertexEquiv (Δ[1] ⊗ Δ[1]) D).symm
        (functorVertexEquiv (Δ[1] ⊗ Δ[1]) D (F ≫ f)))
      rw [Equiv.symm_apply_apply]
      exact hf.2 F hF)

/-- 概要：pushout 図式の後合成は周囲の内部 Hom の後合成を回収する。
方針：全部分複体への持ち上げの包含の式。
規約：全単体での厳密等号。使われ方：span 射影との可換性。 -/
lemma pushoutDiagramsPostcomp_ι {C D : SSet.{u}} (f : C ⟶ D)
    (hf : PreservesSConstructionData f) :
    pushoutDiagramsPostcomp f hf ≫ (fullSubcomplexOnVertices _ IsPushoutDiagramVertex).ι =
      (fullSubcomplexOnVertices _ IsPushoutDiagramVertex).ι ≫ (ihom (Δ[1] ⊗ Δ[1])).map f := rfl

/-- 概要：pushout 図式の後合成は入力 span への射影と厳密に可換。
方針：前合成と後合成の自然性を使う。
規約：追加の選択条件は不要。使われ方：同じ入力 span 上の二つの選択の比較。 -/
lemma pushoutDiagramsPostcomp_projection {C D : SSet.{u}} (f : C ⟶ D)
    (hf : PreservesSConstructionData f) :
    pushoutDiagramsPostcomp f hf ≫ pushoutProjection D =
      pushoutProjection C ≫ (ihom (horn 2 0 : SSet.{u})).map f := by
  change (pushoutDiagramsPostcomp f hf ≫
      (fullSubcomplexOnVertices _ IsPushoutDiagramVertex).ι) ≫
      (pre spanSquareBoundary).app D = _
  rw [pushoutDiagramsPostcomp_ι, Category.assoc,
    (pre spanSquareBoundary).naturality f]
  rfl

/-- 概要：完全関手で移した pushout の族と移した入力に選んだ族は関手として同型。
方針：二つの族の入力 span の厳密な一致を確認し、可縮な選択空間で比較する。
規約：源・標的は安定な quasicategory。使われ方：選択によらない McCarthy の pushout の比較。 -/
def stablePushoutSection_postcompIso {C D : SSet.{u}} [Quasicategory C] [IsStable C]
    [Quasicategory D] [IsStable D] (f : C ⟶ D) (hf : PreservesCofiberData f) :
    FunctorIso (stablePushoutSection C ≫ pushoutDiagramsPostcomp f hf.toSConstructionData)
      ((ihom (horn 2 0 : SSet.{u})).map f ≫ stablePushoutSection D) :=
  stablePushoutFamiliesIso ((ihom (horn 2 0 : SSet.{u})).map f) _ _ (by
    rw [Category.assoc, pushoutDiagramsPostcomp_projection, ← Category.assoc,
      stablePushoutSection_projection, Category.id_comp]) (by
    rw [Category.assoc, stablePushoutSection_projection, Category.comp_id])

end SerrePositivity.KST.SConstruction
