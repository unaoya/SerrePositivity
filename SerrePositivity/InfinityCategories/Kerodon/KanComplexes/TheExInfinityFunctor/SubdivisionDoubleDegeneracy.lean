module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.DegeneracyFibers

/-!
# 二重の拡張退化と通常の退化

概要：二つの隣接した拡張退化の合成を通常の退化との合成へ移す。
方針：singleton 上で二つの特別な頂点を分け、通常の退化の恒等式を使う。
規約：Moss 2020 Lemma 26 (7) より強い未切断の式を先に証明し、原典の式を後合成で得る。
使われ方：Ex の pairing 候補を二度適用すると退化すること。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder

/--
概要：二重の拡張退化の合成は通常の隣接した退化を前に合成したものに等しい。
方針：和の保存から singleton に帰着し、特別な二頂点と残りを分ける。
規約：Moss 2020 Lemma 26 (7) に用いる、原典より強い未切断の式。
使われ方：pairing 候補を二度適用した単体の退化性。
-/
theorem finiteChainDegeneracy_double (n : ℕ) (k : Fin (n + 1)) :
    (finiteChainDegeneracy.{u} n k ∘ finiteChainDegeneracy (n + 1) k.castSucc) =
      (finiteChainDegeneracy n k ∘ fun s => s.map (liftedDegeneracy (n + 1) k.succ)) := by
  apply finiteChainUnion_ext
    ((finiteChainDegeneracy_preservesUnion n k).comp
      (finiteChainDegeneracy_preservesUnion (n + 1) k.castSucc))
    ((finiteChainDegeneracy_preservesUnion n k).comp
      (finiteChainMap_preservesUnion (liftedDegeneracy (n + 1) k.succ)))
  intro i
  change finiteChainDegeneracy n k
      (finiteChainDegeneracy (n + 1) k.castSucc (finiteChainSingleton i)) =
    finiteChainDegeneracy n k ((finiteChainSingleton i).map (liftedDegeneracy (n + 1) k.succ))
  rw [finiteChainDegeneracy_singleton, finiteChainMap_singleton]
  by_cases h₁ : i = ULift.up k.castSucc.succ
  · rw [ite_eq_left h₁]
    subst i
    have hd : liftedDegeneracy.{u} (n + 1) k.succ (ULift.up k.castSucc.succ) = ULift.up k.succ := by
      calc
        _ = liftedDegeneracy (n + 1) k.succ (ULift.up k.succ.castSucc) :=
          congrArg (liftedDegeneracy (n + 1) k.succ) (ULift.ext (Fin.ext rfl))
        _ = _ := liftedDegeneracy_castSucc (n + 1) k.succ
    rw [finiteChainDegeneracy_initialSegment, liftedDegeneracy_castSucc, hd,
      finiteChainDegeneracy_singleton, ite_eq_left rfl]
  · rw [ite_eq_right h₁]
    by_cases h₂ : i = ULift.up k.succ.succ
    · subst i
      have hd : liftedDegeneracy.{u} (n + 1) k.castSucc (ULift.up k.succ.succ) = ULift.up k.succ :=
        (liftedDegeneracy_next_fiber n k _).mpr rfl
      rw [hd, finiteChainDegeneracy_singleton, ite_eq_left rfl, liftedDegeneracy_succ,
        finiteChainDegeneracy_singleton, ite_eq_left rfl]
    · have hl : liftedDegeneracy (n + 1) k.castSucc i ≠ ULift.up k.succ :=
        fun h => h₂ ((liftedDegeneracy_next_fiber n k i).mp h)
      have hr : liftedDegeneracy (n + 1) k.succ i ≠ ULift.up k.succ := by
        intro h
        rcases (liftedDegeneracy_self_fiber n k i).mp h with h | h
        · exact h₁ h
        · exact h₂ h
      rw [finiteChainDegeneracy_singleton, ite_eq_right hl,
        finiteChainDegeneracy_singleton, ite_eq_right hr]
      apply congrArg finiteChainSingleton
      apply ULift.ext
      exact congrArg
        (fun f : SimplexCategory.mk (n + 2) ⟶ SimplexCategory.mk n => f i.down)
        (SimplexCategory.σ_comp_σ (i := k) (j := k) le_rfl)

/--
概要：細分上の二重の拡張退化を通常の退化との合成へ移す。
方針：有限鎖の合成則を nerve の各頂点に適用する。
規約：Moss 2020 Lemma 26 (7) の未切断の強い形。
使われ方：Ex の二重の pairing 候補の計算。
-/
@[reassoc] theorem subdivisionDegeneracyAt_double (n : ℕ) (k : Fin (n + 1)) :
    subdivisionDegeneracyAt.{u} (n + 1) k.castSucc ≫ subdivisionDegeneracyAt n k =
      SimplexCategory.sd.map (SimplexCategory.σ k.succ) ≫ subdivisionDegeneracyAt n k := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  exact congrFun (finiteChainDegeneracy_double n k) (s.obj i)

/--
概要：複雑度で切った二重の拡張退化の式。
方針：未切断の式に複雑度作用素を後合成する。
規約：Moss 2020 Lemma 26 (7)、原典の n はこの宣言の n+1。
使われ方：regular pairing の型 II 条件の検証。
-/
@[reassoc] theorem subdivisionDegeneracyAt_double_cut (n : ℕ) (k : Fin (n + 1)) :
    subdivisionDegeneracyAt.{u} (n + 1) k.castSucc ≫ subdivisionDegeneracyAt n k ≫
      subdivisionCutAt (SimplexCategory.mk n) k =
    SimplexCategory.sd.map (SimplexCategory.σ k.succ) ≫ subdivisionDegeneracyAt n k ≫
      subdivisionCutAt (SimplexCategory.mk n) k := by
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ subdivisionCutAt (SimplexCategory.mk n) k) (subdivisionDegeneracyAt_double n k)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
