module

public import SerrePositivity.EInfinity.SimplexCuts.DeletedCutFaces
public import SerrePositivity.EInfinity.SimplexCuts.GeneratorDegreeTransfers
public import SerrePositivity.EInfinity.SimplexCuts.OutputBoundaryTerms

/-!
# 指定された削除面の生成元による実テンソル

Berger–Fresse §2.2.6–7、M14 L09a。
既存のdeletedCutTensorを同じ更新次数の指定面で読み、次数の等式による移送を整理する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C160：各因子を同じ次数の等式で移した純粋テンソルは、共通の終域次数で一致。 -/
lemma tensorValue_cast_target_congr (K : Complex A) (n : ℕ) (d e : Fin n → ℕ)
    (h : d = e) (v : ∀ i, K.X (-(d i : ℤ))) (w : ∀ i, K.X (-(e i : ℤ)))
    (hv : ∀ i, v i = (eqToHom (congrArg (fun t : ℤ => K.X t)
      (congrArg (fun k : ℕ => -(k : ℤ)) (congrFun h i).symm))).hom (w i))
    (z : ℤ) (hd : -(degreeSum n d : ℤ) = z) (he : -(degreeSum n e : ℤ) = z) :
    (eqToHom (congrArg (fun t : ℤ => (power K n).X t) hd)).hom (tensorValue K n d v) =
      (eqToHom (congrArg (fun t : ℤ => (power K n).X t) he)).hom (tensorValue K n e w) := by
  subst e
  have hsame : v = w := by
    funext i
    simpa only [eqToHom_refl, ModuleCat.id_apply] using hv i
  subst w
  rfl

/-- C161：元の削除テンソルは、各色の指定削除面の生成元の同じ純粋テンソル。 -/
lemma deletedCutTensor_eq_faces {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (ha : 0 < outputDegree s v a)
    (j : Fin (outputDegree s v a + 1)) (x : S _⦋q⦌)
    (h : -(degreeSum r (Function.update (outputDegree s v) a
      (outputDegree s v a - 1)) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
    deletedCutTensor A S s v a ha j x =
      (eqToHom (congrArg (fun t : ℤ => (power (chains A S) r).X t) h)).hom
        (tensorValue (chains A S) r
          (Function.update (outputDegree s v) a (outputDegree s v a - 1))
          (fun c => gen A S _ (S.map (deletedCutFace s v a ha j c).op x))) := by
  dsimp only [deletedCutTensor]
  congr 1
  apply congrArg (tensorValue (chains A S) r
    (Function.update (outputDegree s v) a (outputDegree s v a - 1)))
  funext c
  split_ifs with hc
  · subst c
    rw [deletedCutFace, dite_eq_left rfl, gen_cast_source]
    · have hcast (M N : ModuleCat A) (hMN : M = N) (y : M) :
          HEq ((eqToHom hMN).hom y) y := by
        subst N
        rfl
      have he : Function.update (outputDegree s v) a (outputDegree s v a - 1) a =
          outputDegree s v a - 1 := Function.update_self _ _ _
      have hh := hcast _ _
        (congrArg (fun k : ℕ => (chains A S).X (-(k : ℤ))) he.symm)
        (gen A S (outputDegree s v a - 1) (S.map (boundaryFace _ ha j ≫ face s v a).op x))
      apply eq_of_heq
      refine HEq.trans ?_ hh.symm
      simp only [eq_mpr_eq_cast, cast_heq]
    · exact Function.update_self _ _ _
  · rw [deletedCutFace, dite_eq_right hc, gen_cast_source]
    exact Function.update_of_ne hc _ _

end SerrePositivity.EInfinity.SimplexCuts
