module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeTensorComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeConeTopEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardHomParameterNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedSimplexNativeParameterEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.AWCutFaces

/-!
概要：実A09逆射とA12の像の各AW切断を元の実標準AW切断項へ同定する。
方針：同じ自由生成元のtensor成分と錐・パラメータの最上位評価を前面・後面で合わせる。
規約：全標準単体パラメータ・全切断点と指定比較射を保持する既存構成の評価則。
使われ方：HA 1.2.4、IS-W2 B02のraw AW全切断和の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory MonoidalCategory CochainComplex HomComplex HomologicalComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial TensorProduct
variable {A : Type u} [CommRing A]

/-- 元の実パラメータを入れたA09逆射の各自由生成元のAW切断は、同じ実標準AW項。 -/
theorem reflectedBKFreeTensor_inverse_cut (P : Complex A)
    (X : CosimplicialObject (Complex A)) (m : SimplexCategory)
    (α : (standardHomSpace (R := A) P ((productTotalFunctor A).obj X)).obj (Opposite.op m))
    (j : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) (N : ℕ) (c : Fin (N + 1))
    (s : ((reflectedNormalizedBKSmallWeight A).obj j).obj (Opposite.op ⦋N⦌))
    (a : ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)).obj
      (Opposite.op ⦋N⦌)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
    let S := (reflectedNormalizedBKSmallWeight A).obj j
    let B := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)
    let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    let f := liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α
    let Y := (homDiagramFunctor P).obj X
    let γ := homToNormalizedBousfieldKan P X ≫ (normalizedBKReverseHomotopyEquiv Y).hom ≫
      (reflectedNormalizedBKSmallHomIso A Y).hom
    let t := (freeTensorDiagramHomIso A (normalizedBKSmallDiagram A Y)
      (reflectedNormalizedBKSmallWeight A)).inv.app (Opposite.op m)
        (((truncatedDoldKanFunctor A).map γ).app (Opposite.op m)
          ((standardDoldKanSpaceMap (R := A) P T).app (Opposite.op m) α))
    (t.app j).f (-(N : ℤ)) (ιTensorObj (freeNegativeChains (A := A) S)
      (freeNegativeChains (A := A) B) (-(c.val : ℤ)) (-((N - c.val : ℕ) : ℤ)) (-(N : ℤ))
      (by have := awDegrees N c; omega)
      (freeNegativeGenerator S c.val (S.map (awFront N c).op s) ⊗ₜ[A]
        freeNegativeGenerator B (N - c.val) (B.map (awBack N c).op a))) =
      awTerm (g.app _ s).val (f.app _ a).val Finset.univ ⟨c, Finset.mem_univ c⟩
        (-(N : ℤ)) (by simp) := by
  dsimp only
  let T := (productTotalFunctor A).obj X
  let Q := (doubleOppositeDiagram X).obj (AsSmall.down.obj j)
  let S := (reflectedNormalizedBKSmallWeight A).obj j
  let B := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj m)
  let g := (reversedWeightPointwiseBousfieldKanCone X).app (AsSmall.down.obj j) ≫
    (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
      (forget (ModuleCat A))).inv
  let f := liftedStandardSimplexIso.{u}.hom.app m ≫ SSet.yonedaEquiv.symm α
  let sf := S.map (awFront N c).op s
  let ab := B.map (awBack N c).op a
  have ht := reflectedBKFreeTensor_inverse_component P X m
    ((standardDoldKanSpaceMap (R := A) P T).app (Opposite.op m) α)
    c.val (-((N - c.val : ℕ) : ℤ)) (-(N : ℤ)) (by have := awDegrees N c; omega) j
    (freeNegativeGenerator S c.val sf) (freeNegativeGenerator B (N - c.val) ab)
  have hη := reflectedBKFreeCone_generator_top X (AsSmall.down.obj j) c.val sf
  have hmη := standardHomParameter_map g (awFront N c) s
  have hη' := hη.trans (congrArg (standardTopEval (R := A) T Q c.val) hmη)
  have hβ := normalizedSimplexHomEquiv_native_generator A P T m α (N - c.val) ab
  have hmβ := standardHomParameter_map f (awBack N c) a
  have hβ' := hβ.trans (congrArg (standardTopEval (R := A) P T (N - c.val)) hmβ)
  have hc := congrArg₂ (fun gg : Homogeneous T Q (-(c.val : ℤ)) =>
      fun ff : Homogeneous P T (-((N - c.val : ℕ) : ℤ)) =>
        compose A (D := Complex A) (p := -((N - c.val : ℕ) : ℤ)) (q := -(c.val : ℤ))
          (n := -(N : ℤ)) (x := P) (y := T) (z := Q) gg ff
            (by have := awDegrees N c; omega)) hη' hβ'
  exact ht.trans (hc.trans (awTerm_univ_top_faces (g.app _ s) (f.app _ a) c).symm)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
