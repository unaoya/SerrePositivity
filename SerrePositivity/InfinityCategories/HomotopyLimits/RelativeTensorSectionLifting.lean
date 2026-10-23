module

public import SerrePositivity.InfinityCategories.HomotopyLimits.TensorFamilyCurrying
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightFibrationLocalFamily
public import SerrePositivity.InfinityCategories.F1.Scaffold.UniversalScaffoldEvaluation

/-!
概要：相対 Hom の頂点 fiber の可縮性から、元の積図式の切断制限の全境界充填を得る。
方針：全パラメータの指数則と相対持ち上げを、元の図式の全境界へ移す。
規約：底 K は任意の単体集合。使われ方：HTT 5.5.4.5(2) の余極限比較辺の局所性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 各頂点の相対 Hom fiber が可縮なら、積図式の切断の元の制限は全境界を持ち上げる。 -/
lemma relativeFunctorPre_tensor_trivial_of_vertexFibers {A D K E B : SSet.{u}}
    (i : D ⟶ A) [Mono i] (p : E ⟶ B) [RightFibration p]
    (sq : internalHom.PullbackObjObj i p) (g : A ⊗ K ⟶ B)
    (h : ∀ (k : K _⦋0⦌) (b : sq.pt _⦋0⦌),
      sq.snd.app (Opposite.op ⦋0⦌) b = (curry g).app (Opposite.op ⦋0⦌) k →
      IsContractibleKan (vertexFiber sq.π b)) :
    TrivialKanFibration (relativeFunctorPre p g (i ▷ K)) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro u v s
  let j := K ◁ (boundary n).ι
  have : Mono j := (tensorLeft K).map_mono (boundary n).ι
  let d := tensorFamilyCurry (relativeFunctorUncurry v)
  let l := tensorFamilyCurry (relativeFunctorUncurry u)
  have hd : d ≫ (ihom D).map p = (fst K Δ[n] ≫ curry g) ≫ (pre i).app B := by
    rw [← tensorFamilyCurry_post, relativeFunctorUncurry_projection,
      tensorFamilyCurry_constant, ← curry_pre_app, Category.assoc]
  have hl : l ≫ (pre i).app E = j ≫ d := by
    have he := congrArg relativeFunctorUncurry s.w
    rw [SerrePositivity.InfinityCategories.relativeFunctorUncurry_pre,
      SerrePositivity.InfinityCategories.relativeFunctorUncurry_parameter] at he
    change tensorFamilyCurry (relativeFunctorUncurry u) ≫ (pre i).app E = _
    rw [← tensorFamilyCurry_source, he, tensorFamilyCurry_parameter]
  have hb : l ≫ (ihom A).map p = j ≫ fst K Δ[n] ≫ curry g := by
    change tensorFamilyCurry (relativeFunctorUncurry u) ≫ (ihom A).map p = _
    rw [← tensorFamilyCurry_post, relativeFunctorUncurry_projection, tensorFamilyCurry_constant]
    rfl
  obtain ⟨L, hLj, hLd, hLb⟩ := relativeHomFamily_exists_extension_over_base
    i p sq (curry g) h j d (fst K Δ[n]) hd l hl hb
  have hLp : tensorFamilyUncurry L ≫ p = fst (A ⊗ K) Δ[n] ≫ g := by
    apply tensorFamilyCurry_injective
    rw [tensorFamilyCurry_post, tensorFamilyCurry_uncurry, hLb, tensorFamilyCurry_constant]
  let W := relativeFunctorCurry (tensorFamilyUncurry L) hLp
  refine CommSq.HasLift.mk' { l := W, fac_left := ?_, fac_right := ?_ }
  · apply relativeFunctorUncurry_injective p g
    rw [SerrePositivity.InfinityCategories.relativeFunctorUncurry_parameter,
      relativeFunctorUncurry_curry]
    apply tensorFamilyCurry_injective
    rw [tensorFamilyCurry_parameter, tensorFamilyCurry_uncurry, hLj]
  · apply relativeFunctorUncurry_injective p ((i ▷ K) ≫ g)
    rw [SerrePositivity.InfinityCategories.relativeFunctorUncurry_pre,
      relativeFunctorUncurry_curry]
    apply tensorFamilyCurry_injective
    rw [tensorFamilyCurry_source, tensorFamilyCurry_uncurry, hLd]

end SerrePositivity.InfinityCategories.HomotopyLimits
