module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UpdatedTensorDifferential
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.DeletedGeneratorDifferential
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HomogeneousFactorLinearity

/-!
模型。文献の定義との比較は後で
# 正次数の因子微分と同じ指定削除テンソルの和

Berger–Fresse §2.2.7、M14 L09の証明分割。
同じ因子の微分・面和・更新次数のテンソルを、既存のdeletedCutTensorへ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C280：正次数因子の同じ微分は、同じ指定削除テンソルの交代和。 -/
lemma cast_tensorValueDifferentialFactor_eq_sum_deletedCutTensor (S : SSet.{0})
    {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1))
    (a : Fin r) (ha : 0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a) (x : S _⦋q⦌)
    (h : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v) : ℤ) + 1 = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
    (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r).X z) h)).hom
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValueDifferentialFactor (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v)
          (fun b => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v b) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v b).op x)) a) =
      ∑ j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a + 1),
        (-1 : ℤ) ^
          ((∑ b ∈ Finset.univ.filter (fun b : Fin r => b < a), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v b) + j.val) •
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedCutTensor A S s v a ha j x := by
  let K := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S
  let d := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v
  let e := Function.update d a (d a - 1)
  let G (j : Fin (d a + 1)) (b : Fin r) :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (e b) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedCutFace s v a ha j b).op x)
  let w := Function.update (G 0) a (∑ j, (-1 : ℤ) ^ j.val • G j a)
  let W (j : Fin (d a + 1)) := Function.update (G 0) a ((-1 : ℤ) ^ j.val • G j a)
  have hd : ∀ b, d b = e b + if b = a then 1 else 0 := by
    intro b
    by_cases hb : b = a
    · subst b
      simp only [e, Function.update_self, ite_true]
      dsimp only [d]
      omega
    · simp only [e, Function.update_of_ne hb, hb, ite_false, Nat.add_zero]
  have ht : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r e : ℤ) = -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r d : ℤ) + 1 := by
    have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r e + 1 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r d := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum_delete d a ha
    omega
  have hw : ∀ b, b ≠ a → HEq
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (d b) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v b).op x)) (w b) := by
    intro b hb
    dsimp only [w]
    rw [Function.update_of_ne hb]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedCutFace_gen_other_heq A S s v a ha 0 b hb x
  have hv : HEq (K.d (-(d a : ℤ)) (-(d a : ℤ) + 1)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (d a) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v a).op x))) (w a) := by
    dsimp only [w]
    rw [Function.update_self]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen_d_heq_sum_deletedCutFace A S s v a ha x
  have hf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValueDifferentialFactor_eq_updated_tensor K r d e
    (fun b => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (d b) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v b).op x)) w a hd hv hw ht
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue_sum_factor K r e w W a
    (by simp only [w, W, Function.update_self])
    (by intro j b hb; simp only [W, w, Function.update_of_ne hb])
  have hz (j : Fin (d a + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K r e (W j) =
      (-1 : ℤ) ^ j.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K r e (G j) := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue_zsmul_factor K r e (W j) (G j) a ((-1 : ℤ) ^ j.val)
    · simp only [W, Function.update_self]
    · intro b hb
      dsimp only [W]
      rw [Function.update_of_ne hb]
      dsimp only [G]
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedCutFace_other_eq s v a ha j 0 b hb]
  simp_rw [hz] at hs
  have he : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r e : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1 := ht.trans h
  have hg (j : Fin (d a + 1)) :
      (eqToHom (congrArg (fun z : ℤ => (power K r).X z) he)).hom
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K r e (G j)) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedCutTensor A S s v a ha j x :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedCutTensor_eq_faces A S s v a ha j x he).symm
  have step {M N P : ModuleCat A} (hMN : M = N) (hNP : N = P) (y : M) :
      (eqToHom hNP).hom ((eqToHom hMN).hom y) = (eqToHom (hMN.trans hNP)).hom y := by
    subst N
    subst P
    rfl
  rw [hf, map_zsmul, step, hs]
  simp only [map_sum, map_zsmul, Finset.smul_sum, smul_smul, ← pow_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [hg j]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
