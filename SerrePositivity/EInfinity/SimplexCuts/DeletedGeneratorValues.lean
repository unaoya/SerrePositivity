module

public import SerrePositivity.EInfinity.SimplexCuts.DeletedFaceTensors

/-!
# 指定削除面の同じ正規化生成元

Berger–Fresse §2.2.7、M14 L09の証明分割。
既存の始域次数の移送を異種等式で読み、変更しない因子と選んだ面の因子を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C273：指定面の始域の等式移送は、同じ生成元の異種等式を与える。 -/
lemma gen_cast_source_heq (S : SSet.{0}) {n n' q : ℕ} (h : n = n')
    (f : (⦋n'⦌ : SimplexCategory) ⟶ ⦋q⦌) (x : S _⦋q⦌) :
    HEq (gen A S n (S.map (eqToHom (congrArg SimplexCategory.mk h) ≫ f).op x))
      (gen A S n' (S.map f.op x)) := by
  subst n'
  simp only [eqToHom_refl, Category.id_comp]
  rfl

/-- C274：変更しない色の指定面は、削除面番号によらず同じ射。 -/
lemma deletedCutFace_other_eq {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (a : Fin r) (ha : 0 < outputDegree s v a)
    (j j' : Fin (outputDegree s v a + 1)) (b : Fin r) (hb : b ≠ a) :
    deletedCutFace s v a ha j b = deletedCutFace s v a ha j' b := by
  simp only [deletedCutFace, dite_eq_right hb]

/-- C275：変更しない色の元の生成元と、指定削除面の同じ因子の生成元は異種等式で一致。 -/
lemma deletedCutFace_gen_other_heq (S : SSet.{0}) {m q r : ℕ}
    (s : Cut m q) (v : Surjection.Word r (m + 1)) (a : Fin r)
    (ha : 0 < outputDegree s v a) (j : Fin (outputDegree s v a + 1))
    (b : Fin r) (hb : b ≠ a) (x : S _⦋q⦌) :
    HEq (gen A S (outputDegree s v b) (S.map (face s v b).op x))
      (gen A S (Function.update (outputDegree s v) a (outputDegree s v a - 1) b)
        (S.map (deletedCutFace s v a ha j b).op x)) := by
  rw [deletedCutFace, dite_eq_right hb]
  exact (gen_cast_source_heq A S (Function.update_of_ne hb _ _) (face s v b) x).symm

/-- C276：選んだ色の標準面の生成元と、同じ指定削除面の生成元は異種等式で一致。 -/
lemma deletedCutFace_gen_self_heq (S : SSet.{0}) {m q r : ℕ}
    (s : Cut m q) (v : Surjection.Word r (m + 1)) (a : Fin r)
    (ha : 0 < outputDegree s v a) (j : Fin (outputDegree s v a + 1)) (x : S _⦋q⦌) :
    HEq (gen A S (outputDegree s v a - 1)
        (S.map (boundaryFace _ ha j ≫ face s v a).op x))
      (gen A S (Function.update (outputDegree s v) a (outputDegree s v a - 1) a)
        (S.map (deletedCutFace s v a ha j a).op x)) := by
  rw [deletedCutFace, dite_eq_left rfl]
  exact (gen_cast_source_heq A S (Function.update_self _ _ _)
    (boundaryFace _ ha j ≫ face s v a) x).symm

end SerrePositivity.EInfinity.SimplexCuts
