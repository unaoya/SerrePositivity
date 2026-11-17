module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechSquareTriangle
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechIso
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareComparison

/-!
概要：表示の同型に沿って、同じ閉中心の native な四角形の完全性を移す。
方針：実際の引き戻しと、等しい逆像被覆の細分の同型を使う。
規約：基底・中心・スカラーを保持し、完全性を追加仮定にしない。
使われ方：Proj の計算を実際のブローアップと有限ファイバー冪へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry
universe u v w

/-- 等しい被覆の恒等添字の細分は、実際の複体の同型。 -/
theorem openCoverCechRefinementMap_isIso_of_eq {T : Type u} [TopologicalSpace T]
    {R : Type w} [CommRing R] {ι : Type} [LinearOrder ι]
    (P : (Opens T)ᵒᵖ ⥤ ModuleCat.{v} R) (U V : ι → Opens T)
    (h : V = U) (hV : ∀ i, V i ≤ U i) :
    IsIso (openCoverCechRefinementMap P U V id hV) := by
  subst V
  rw [openCoverCechRefinementMap_id]
  infer_instance

variable {R S : Type u} [CommRing R] [CommRing S]
variable {X Y Z : Scheme.{u}} {ι : Type} [LinearOrder ι]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ閉中心を保つ表示の同型は、native な四角形の全複体の完全性を比較する。
BST13 Lemma 3.9・BS17 Lemma 4.6(i) に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem schemeStructurePerfectCechSquare_iso_acyclic_iff
    (v : Y ⟶ Z) [IsIso v] (f : X ⟶ Y) (g : X ⟶ Z) (he : f ≫ v = g)
    (q : R →+* S) (φZ : R →+* Γ(Z, ⊤)) (φY : R →+* Γ(Y, ⊤))
    (ψ : S →+* Γ(X, ⊤)) (hφY : φY = v.appTop.hom.comp φZ)
    (hcommZ : g.appTop.hom.comp φZ = ψ.comp q)
    (hcommY : f.appTop.hom.comp φY = ψ.comp q)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)
    (hZ : ∀ O, (p : Z.presheaf.obj O) = 0)
    (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
    (hX : ∀ O, (p : X.presheaf.obj O) = 0) (U : ι → Z.Opens) :
    (schemeStructurePerfectCechSquare g q φZ ψ hcommZ p hp hR hS hZ hX U).totalComplex.Acyclic ↔
      (schemeStructurePerfectCechSquare f q φY ψ hcommY p hp hR hS hY hX
        (fun i ↦ v ⁻¹ᵁ U i)).totalComplex.Acyclic := by
  let m := schemeStructurePerfectCechSquare_triangleMap v f g he q φZ φY ψ hφY
    hcommZ hcommY p hp hR hS hZ hY hX U (fun i ↦ v ⁻¹ᵁ U i) (fun _ ↦ le_rfl)
  have hl : IsIso m.left := by
    change IsIso (schemeStructurePerfectCechRefinedPullbackMap v p hp hZ hY
      U (fun i ↦ v ⁻¹ᵁ U i) id (fun _ ↦ le_rfl))
    rw [← schemeStructurePerfectCechPullbackMap_eq_refined]
    exact schemeStructurePerfectCechPullbackMap_isIso v p hp hZ hY U
  have hr : IsIso m.right := by
    change IsIso (openCoverCechRefinementMap (frobeniusRingDiagram X.presheaf p hp hX)
      (fun i ↦ g ⁻¹ᵁ U i) (fun i ↦ f ⁻¹ᵁ (v ⁻¹ᵁ U i)) id _)
    apply openCoverCechRefinementMap_isIso_of_eq
    funext i
    rw [← he, Scheme.Hom.comp_preimage]
  apply m.totalComplex_acyclic_iff_of_cones
  · apply cechRefinementCone_acyclic_of_quasiIso
    intro k
    infer_instance
  · apply cechRefinementCone_acyclic_of_quasiIso
    intro k
    infer_instance
  · exact Function.bijective_id
  · exact Function.bijective_id

end SerrePositivity.AlgebraicGeometry
