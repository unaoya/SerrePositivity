module

public import SerrePositivity.EInfinity.SimplexCuts.DeletedGeneratorValues
public import SerrePositivity.EInfinity.SimplexCuts.GeneratorDifferentialValues

/-!
# 同じ生成元の微分と指定削除面の全和

Berger–Fresse §2.2.7、M14 L09の証明分割。
既存の標準面の交代和を、同じ更新次数で指定削除面の生成元へ運ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C277：同じ加群の等式移送と各値の異種等式は、整数倍の有限和を保つ。 -/
lemma sum_zsmul_heq {J : Type*} [Fintype J] {M N : ModuleCat A} (h : M = N)
    (c : J → ℤ) (x : J → M) (y : J → N) (hv : ∀ j, HEq (x j) (y j)) :
    HEq (∑ j, c j • x j) (∑ j, c j • y j) := by
  subst N
  have he : x = y := by funext j; exact eq_of_heq (hv j)
  subst y
  rfl

/-- C278：同じ生成元は、指定単体射の合成と逐次の像で厳密に一致する。 -/
lemma gen_map_comp (S : SSet.{0}) {n m q : ℕ}
    (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋m⦌) (g : (⦋m⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (x : S _⦋q⦌) :
    gen A S n (S.map (f ≫ g).op x) = gen A S n (S.map f.op (S.map g.op x)) := by
  congr 1
  exact congrArg (fun h => h x) (S.map_comp g.op f.op)

/-- C279：同じ正次数因子の微分は、更新次数の同じ指定削除面の全和と異種等式で一致。 -/
lemma gen_d_heq_sum_deletedCutFace (S : SSet.{0}) {m q r : ℕ}
    (s : Cut m q) (v : Surjection.Word r (m + 1)) (a : Fin r)
    (ha : 0 < outputDegree s v a) (x : S _⦋q⦌) :
    HEq ((chains A S).d (-(outputDegree s v a : ℤ)) (-(outputDegree s v a : ℤ) + 1)
        (gen A S (outputDegree s v a) (S.map (face s v a).op x)))
      (∑ j : Fin (outputDegree s v a + 1), (-1 : ℤ) ^ j.val •
        gen A S (Function.update (outputDegree s v) a (outputDegree s v a - 1) a)
          (S.map (deletedCutFace s v a ha j a).op x)) := by
  let e := Function.update (outputDegree s v) a (outputDegree s v a - 1)
  let f (j : Fin (outputDegree s v a + 1)) :=
    gen A S (outputDegree s v a - 1) (S.map (boundaryFace _ ha j ≫ face s v a).op x)
  let g (j : Fin (outputDegree s v a + 1)) :=
    gen A S (e a) (S.map (deletedCutFace s v a ha j a).op x)
  have he : e a = outputDegree s v a - 1 := Function.update_self _ _ _
  have hshift : -((outputDegree s v a - 1 : ℕ) : ℤ) = -(outputDegree s v a : ℤ) + 1 := by
    omega
  have ht := gen_d_boundaryFace A S (outputDegree s v a) ha (S.map (face s v a).op x) hshift
  have hu : (chains A S).d (-(outputDegree s v a : ℤ)) (-(outputDegree s v a : ℤ) + 1)
      (gen A S (outputDegree s v a) (S.map (face s v a).op x)) =
      (eqToHom (congrArg (fun z : ℤ => (chains A S).X z) hshift)).hom
        (∑ j, (-1 : ℤ) ^ j.val • f j) := by
    rw [ht, map_sum]
    simp only [map_zsmul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [f]
    rw [gen_map_comp]
  have hcast {M N : ModuleCat A} (hMN : M = N) (y : M) :
      HEq ((eqToHom hMN).hom y) y := by subst N; rfl
  have hp := (heq_of_eq hu).trans
    (hcast (congrArg (fun z : ℤ => (chains A S).X z) hshift) (∑ j, (-1 : ℤ) ^ j.val • f j))
  have hs := sum_zsmul_heq A
    (congrArg (fun n : ℕ => (chains A S).X (-(n : ℤ))) he.symm)
    (fun j : Fin (outputDegree s v a + 1) => (-1 : ℤ) ^ j.val) f g
    (fun j => deletedCutFace_gen_self_heq A S s v a ha j x)
  exact hp.trans hs

end SerrePositivity.EInfinity.SimplexCuts
