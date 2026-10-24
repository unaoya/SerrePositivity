module

public import SerrePositivity.InfinityCategories.Core.EquivalencePathInternalHom

/-!
概要：図式の各点での可逆 path と関手単体集合内の可逆 path の厳密な対応。
方針：可逆 path と内部 Hom の同型を零単体の Yoneda 表示に移す。
規約：端点と始域の制限を実際の射の等式として保持する。
使われ方：三角形の境界 path を相対 path 持ち上げの入力に変換する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：図式を内部 Hom の零単体からの射として表示する全単射。
方針：関手頂点の同値と零単体の Yoneda 同値を合成する。
規約：任意の単体集合 K,X。
使われ方：図式と path の端点の厳密な比較。 -/
noncomputable def functorDiagramPointEquiv (K X : SSet.{u}) :
    (K ⟶ X) ≃ ((Δ[0] : SSet.{u}) ⟶ (ihom K).obj X) where
  toFun f := SSet.yonedaEquiv.symm (functorVertex f)
  invFun v := (functorVertexEquiv K X).symm (SSet.yonedaEquiv v)
  left_inv f := by
    dsimp only
    rw [Equiv.apply_symm_apply]
    exact (functorVertexEquiv K X).symm_apply_apply f
  right_inv v := by
    change SSet.yonedaEquiv.symm
      (functorVertexEquiv K X ((functorVertexEquiv K X).symm (SSet.yonedaEquiv v))) = v
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- 概要：図式の可逆 path を関手単体集合内の可逆 path に移す全単射。
方針：内部 Hom と可逆 path の同型を零単体の表示へ移す。
規約：対象 X は quasicategory、K は任意。
使われ方：指定した境界 path の持ち上げ。 -/
noncomputable def functorDiagramPathEquiv (K X : SSet.{u}) [Quasicategory X] :
    (K ⟶ equivalencePath X) ≃ ((Δ[0] : SSet.{u}) ⟶ equivalencePath ((ihom K).obj X)) where
  toFun Q := functorDiagramPointEquiv K (equivalencePath X) Q ≫
    (equivalencePathInternalHomIso K X).inv
  invFun L := (functorDiagramPointEquiv K (equivalencePath X)).symm
    (L ≫ (equivalencePathInternalHomIso K X).hom)
  left_inv Q := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Equiv.symm_apply_apply]
  right_inv L := by
    simp only [Equiv.apply_symm_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 概要：図式の零単体表示は標的への後合成を保つ。
方針：内部 Hom の作用と関手頂点の後合成を比較する。
規約：任意の射 e。
使われ方：path の両端の表示。 -/
lemma functorDiagramPointEquiv_postcomp {K X Y : SSet.{u}} (f : K ⟶ X) (e : X ⟶ Y) :
    functorDiagramPointEquiv K X f ≫ (ihom K).map e =
      functorDiagramPointEquiv K Y (f ≫ e) := by
  change SSet.yonedaEquiv.symm (functorVertex f) ≫ (ihom K).map e =
    SSet.yonedaEquiv.symm (functorVertex (f ≫ e))
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

/-- 概要：図式の零単体表示は始域の制限を保つ。
方針：内部 Hom の前合成と関手頂点の表示を比較する。
規約：任意の射 i。
使われ方：境界での始点の等式。 -/
lemma functorDiagramPointEquiv_precomp {A B X : SSet.{u}} (i : A ⟶ B) (f : B ⟶ X) :
    functorDiagramPointEquiv B X f ≫ (pre i).app X =
      functorDiagramPointEquiv A X (i ≫ f) := by
  change SSet.yonedaEquiv.symm (functorVertex f) ≫ (pre i).app X =
    SSet.yonedaEquiv.symm (functorVertex (i ≫ f))
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

/-- 概要：path の図式の対応は両端を厳密に保つ。
方針：内部 Hom 比較の端点公式と零単体表示の後合成の自然性。
規約：端点 j は任意。
使われ方：相対持ち上げの始点と終点。 -/
lemma functorDiagramPathEquiv_endpoint {K X : SSet.{u}} [Quasicategory X]
    (Q : K ⟶ equivalencePath X) (j : Fin 2) :
    functorDiagramPathEquiv K X Q ≫ equivalencePathEndpoint _ j =
      functorDiagramPointEquiv K X (Q ≫ equivalencePathEndpoint X j) := by
  change (functorDiagramPointEquiv K (equivalencePath X) Q ≫
    (equivalencePathInternalHomIso K X).inv) ≫ _ = _
  rw [Category.assoc, ← equivalencePathInternalHomIso_endpoint K X j,
    Iso.inv_hom_id_assoc, functorDiagramPointEquiv_postcomp]

/-- 概要：path の図式の対応は始域の制限を厳密に保つ。
方針：内部 Hom 比較の制限公式と零単体表示の前合成自然性。
規約：制限する射 i は任意。
使われ方：持ち上げた図式が元の境界 path を保持することの検証。 -/
lemma functorDiagramPathEquiv_precomp {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (Q : B ⟶ equivalencePath X) :
    functorDiagramPathEquiv B X Q ≫ equivalencePathMap ((pre i).app X) =
      functorDiagramPathEquiv A X (i ≫ Q) := by
  apply (cancel_mono (equivalencePathInternalHomIso A X).hom).mp
  rw [Category.assoc, equivalencePathInternalHomIso_pre]
  change (functorDiagramPointEquiv B (equivalencePath X) Q ≫
    (equivalencePathInternalHomIso B X).inv) ≫
      ((equivalencePathInternalHomIso B X).hom ≫ (pre i).app (equivalencePath X)) =
    (functorDiagramPointEquiv A (equivalencePath X) (i ≫ Q) ≫
      (equivalencePathInternalHomIso A X).inv) ≫ (equivalencePathInternalHomIso A X).hom
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact functorDiagramPointEquiv_precomp i Q

end SerrePositivity.InfinityCategories
