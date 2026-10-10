module

public import SerrePositivity.HomologicalAlgebra.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # 平坦な係数拡大と Tor

第2変数の射影分解を係数拡大し、テンソル積との可換性とホモロジーの保存を合わせる。
任意の次数で、両変数を係数拡大した Tor と元の Tor の係数拡大を線形同値にする。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory Limits MonoidalCategory TensorProduct

set_option backward.isDefEq.respectTransparency false

/-- 圏論的係数拡大のスカラー作用を、指定された代数構造によるテンソル積へ移す。 -/
noncomputable def extendScalarsObjEquivTensor
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap A B)).obj M ≃ₗ[B] B ⊗[A] M := by
  let B' := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  let eB : B' ≃ₗ[A] B :=
    { toFun := id, invFun := id, left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl,
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a b ↦ by
        dsimp [B', ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj'] at b ⊢
        exact (Algebra.smul_def a b).symm }
  let e := TensorProduct.congr eB (LinearEquiv.refl A M)
  exact AddEquiv.toLinearEquiv e.toAddEquiv (fun b x ↦ by
    induction x using TensorProduct.inductionOn with
    | tmul b' m => rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy])

/-- 平坦な環拡大に関する Tor の基底変更。有限生成性や正則性は不要。 -/
noncomputable def torBaseChangeEquiv
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (i : ℕ) (M N : Type u) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] :
    TorModule B i (B ⊗[A] M) (B ⊗[A] N) ≃ₗ[B] B ⊗[A] TorModule A i M N := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A B)
  let : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A B))
  let P := projectiveResolution (ModuleCat.of A N)
  let PB := F.mapProjectiveResolution P
  let T := tensorLeft (ModuleCat.of A M)
  let TB := tensorLeft (F.obj (ModuleCat.of A M))
  let e : (TB.mapHomologicalComplex _).obj PB.complex ≅
      (F.mapHomologicalComplex _).obj ((T.mapHomologicalComplex _).obj P.complex) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ Functor.Monoidal.μIso F (ModuleCat.of A M) (P.complex.X n))
      (fun n n' _ ↦ by
        change _ ≫ F.map (_ ◁ P.complex.d n n') = (_ ◁ F.map (P.complex.d n n')) ≫ _
        exact (Functor.LaxMonoidal.μ_natural_right F _ _).symm)
  let eM := (extendScalarsObjEquivTensor A B (ModuleCat.of A M)).toModuleIso
  let eN := (extendScalarsObjEquivTensor A B (ModuleCat.of A N)).toModuleIso
  let eTor := (((Tor (ModuleCat B) i).mapIso eM.symm).app (ModuleCat.of B (B ⊗[A] N))) ≪≫
    (((Tor (ModuleCat B) i).obj (F.obj (ModuleCat.of A M))).mapIso eN.symm)
  exact (eTor ≪≫ (PB.isoLeftDerivedObj TB i) ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso e ≪≫
    (((T.mapHomologicalComplex _).obj P.complex).sc i).mapHomologyIso F ≪≫
    F.mapIso (P.isoLeftDerivedObj T i).symm ≪≫
    (extendScalarsObjEquivTensor A B
      (ModuleCat.of A (TorModule A i M N))).toModuleIso).toLinearEquiv

end SerrePositivity
