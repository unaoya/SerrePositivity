module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.GeneratorBoundary
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryFaces
public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.Degrees

/-!
模型。文献の定義との比較は後で
# 指定された整数次数での正規化生成元の微分

Berger–Fresse §2.2.7、M14 L09の証明分割。
同じgen_dを、出力境界項が使う標準面と共通の終域次数で読む。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C260：同じ微分の始域・終域の次数移送は、その微分と可換。 -/
lemma complex_d_cast_source_target (K : Complex A) {i i' j j' : ℤ}
    (hi : i = i') (hj : j = j') (x : K.X i) :
    K.d i' j' ((eqToHom (congrArg K.X hi)).hom x) =
      (eqToHom (congrArg K.X hj)).hom (K.d i j x) := by
  subst i'
  subst j'
  rfl

/-- C261：同じ零次数生成元の境界は、零延長の正次数成分で零。 -/
lemma gen_d_zero (S : SSet.{0}) (x : S _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d 0 1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S 0 x) = 0 := by
  have hz : Limits.IsZero ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X 1) :=
    _root_.SerrePositivity.NegativeTensor.isZero_positive (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S) 1 (by decide)
  have hd : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d 0 1 = 0 := hz.eq_of_tgt _ _
  rw [hd]
  rfl

/-- C262：正次数の同じ生成元の微分を、指定標準面と同じ終域次数で読む。 -/
lemma gen_d_boundaryFace (S : SSet.{0}) (q : ℕ) (hq : 0 < q) (x : S _⦋q⦌)
    (h : -((q - 1 : ℕ) : ℤ) = -(q : ℤ) + 1) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d (-(q : ℤ)) (-(q : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x) =
      ∑ j : Fin (q + 1), (-1 : ℤ) ^ j.val •
        (eqToHom (congrArg (fun t : ℤ => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X t) h)).hom
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (q - 1) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryFace q hq j).op x)) := by
  cases q with
  | zero => omega
  | succ q =>
    have ht := congrArg (fun y =>
      (eqToHom (congrArg (fun t : ℤ => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X t) h)).hom y) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen_d A S q x)
    have hc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.complex_d_cast_source_target A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S)
      (i := -((q + 1 : ℕ) : ℤ)) (i' := -((q + 1 : ℕ) : ℤ))
      (j := -(q : ℤ)) (j' := -((q + 1 : ℕ) : ℤ) + 1) rfl h (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (q + 1) x)
    simp only [eqToHom_refl, ModuleCat.id_apply] at hc
    simp only [map_sum, map_zsmul] at ht
    have ht' := hc.trans ht
    convert ht' using 1
    rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
