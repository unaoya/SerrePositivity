module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.DeletedGeneratorValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.GeneratorDifferentialValues

/-!
模型。文献の定義との比較は後で
# 同じ生成元の微分と指定削除面の全和

Berger–Fresse §2.2.7、M14 L09の証明分割。
既存の標準面の交代和を、同じ更新次数で指定削除面の生成元へ運ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open scoped _root_.Simplicial
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
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S n (S.map (f ≫ g).op x) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S n (S.map f.op (S.map g.op x)) := by
  congr 1
  exact congrArg (fun h => h x) (S.map_comp g.op f.op)

/-- C279：同じ正次数因子の微分は、更新次数の同じ指定削除面の全和と異種等式で一致。 -/
lemma gen_d_heq_sum_deletedCutFace (S : SSet.{0}) {m q r : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a : Fin r)
    (ha : 0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a) (x : S _⦋q⦌) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a : ℤ) + 1)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v a).op x)))
      (∑ j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a + 1), (-1 : ℤ) ^ j.val •
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (Function.update (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v) a (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a - 1) a)
          (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedCutFace s v a ha j a).op x)) := by
  let e := Function.update (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v) a (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a - 1)
  let f (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a + 1)) :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a - 1) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryFace _ ha j ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v a).op x)
  let g (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a + 1)) :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (e a) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedCutFace s v a ha j a).op x)
  have he : e a = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a - 1 := Function.update_self _ _ _
  have hshift : -((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a - 1 : ℕ) : ℤ) = -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a : ℤ) + 1 := by
    omega
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen_d_boundaryFace A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a) ha (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v a).op x) hshift
  have hu : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a : ℤ) + 1)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s v a).op x)) =
      (eqToHom (congrArg (fun z : ℤ => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X z) hshift)).hom
        (∑ j, (-1 : ℤ) ^ j.val • f j) := by
    rw [ht, map_sum]
    simp only [map_zsmul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [f]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen_map_comp]
  have hcast {M N : ModuleCat A} (hMN : M = N) (y : M) :
      HEq ((eqToHom hMN).hom y) y := by subst N; rfl
  have hp := (heq_of_eq hu).trans
    (hcast (congrArg (fun z : ℤ => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X z) hshift) (∑ j, (-1 : ℤ) ^ j.val • f j))
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_zsmul_heq A
    (congrArg (fun n : ℕ => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X (-(n : ℤ))) he.symm)
    (fun j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v a + 1) => (-1 : ℤ) ^ j.val) f g
    (fun j => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletedCutFace_gen_self_heq A S s v a ha j x)
  exact hp.trans hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
