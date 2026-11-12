module
public import SerrePositivity.KST.SConstruction.CubicalLambdaPerfRightActionCoherence
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGNativeRightUnit

/-! # 全 native Perf 右作用の入力合成保存
概要：全 native 関手族の合成を、元の全 Perf 単体への実右作用が厳密に保つ。
方針：HA 抽出の厳密逆律で同じ Λ の実右作用の合成等号へ帰着し、ULift 後に束ねる。
規約：ラベル・前入力・後入力の因子順を保持。使われ方：厳密豊穣 Perf 関手。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E T : Type v)
  [DGCategory A D] [DGCategory A E] [DGCategory A T]
  [Small.{u} D] [Small.{u} E] [Small.{u} T]

/-- 元の全 native Perf 単体の二回右作用は、同じ入力関手族の横合成の作用に等しい。 -/
lemma presentedPerfectDGNativeActionSimplex_comp {N : ℕ}
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (PresentedPerfectDGObject A D) N)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A D E) N)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A E T) N) :
    presentedPerfectDGNativeActionSimplex A E T
        (presentedPerfectDGNativeActionSimplex A D E x s) t =
      presentedPerfectDGNativeActionSimplex A D T x
        (dgFunctorNativeComposeSimplex A D E T s t) := by
  unfold presentedPerfectDGNativeActionSimplex dgFunctorNativeComposeSimplex dgNerveTensorSimplex
  simp only [← cubicalLambdaNativeSimplex_post, simplexHAInverseFunctor_native]
  exact congrArg (cubicalLambdaNativeSimplex A)
    (cubicalLambdaPerfRightAction_associativity A D E T (simplexHAInverseFunctor A x)
      (simplexHAInverseFunctor A s) (simplexHAInverseFunctor A t))

/-- 出力宇宙へ移した元の Kan 入力写像空間の実合成。 -/
def presentedPerfectDGNativeParameterComp :
    presentedPerfectDGNativeParameter A D E ⊗ presentedPerfectDGNativeParameter A E T ⟶
      presentedPerfectDGNativeParameter A D T where
  app n := ↾fun p => ULift.up ((dgFunctorNativeComposition A D E T).app n (p.1.down, p.2.down))
  naturality X Y f := by
    ext p
    rcases p with ⟨s, t⟩
    apply ULift.ext
    exact CategoryTheory.types_congr_hom ((dgFunctorNativeComposition A D E T).naturality f)
      (s.down, t.down)

/-- 元の Kan 入力の合成と全 Perf 単体の実右作用は、全単体的写像として一致する。 -/
lemma presentedPerfectDGNativeCoreAction_comp :
    (presentedPerfectDGNativeCoreAction A D E ⊗ₘ 𝟙 (presentedPerfectDGNativeParameter A E T)) ≫
        presentedPerfectDGNativeCoreAction A E T =
      (α_ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D)) (presentedPerfectDGNativeParameter A D E)
        (presentedPerfectDGNativeParameter A E T)).hom ≫
        (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D)) ⊗ₘ
          presentedPerfectDGNativeParameterComp A D E T) ≫
        presentedPerfectDGNativeCoreAction A D T := by
  ext n p
  rcases p with ⟨⟨x, s⟩, t⟩
  exact presentedPerfectDGNativeActionSimplex_comp A D E T x s.down.val t.down.val

end SerrePositivity.KST.SConstruction
