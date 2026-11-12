module
public import SerrePositivity.KST.SConstruction.CutSConstruction

/-! # 切断作用素と元の S_n の制限の厳密な一致
概要：全高次単体において切断 cofiber 族の各角を元の S_n の端点制限と照合する。
方針：内部 currying の各成分と添字の角の等号を計算する。
規約：頂点だけでなく単体的射の等号。使われ方：切断比較の完全性と Segal 射の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 切断作用素の全角は元の図式の端点制限と全高次単体で厳密に一致する。 -/
lemma cutDiagramFamilyOperator_evaluation (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u})
    (x y : Fin 2) :
    cutDiagramFamilyOperator n k C ≫ (ihom (arNerve n)).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y)) =
      (pre (arNerveMap (cutCornerOrder k x y))).app C := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro a
  change F.app e (α ≫ 𝟙 e) ((arCutSquareMap n k).app e
    ((arNerve n).map (𝟙 e) a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y) e.unop.len)) =
    F.app e (𝟙 d ≫ α) ((arNerveMap (cutCornerOrder k x y)).app e a)
  rw [Category.comp_id, Category.id_comp, CategoryTheory.Functor.map_id_apply]
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app (arCutSquareMap_corner k x y) e) a
  exact congrArg (fun b => F.app e α b) he

/-- 生の gapped 切断作用素の各角は元の端点制限を厳密に保持する。 -/
lemma cutRawFamilyOperator_evaluation (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u})
    (x y : Fin 2) :
    cutRawFamilyOperator n k C ≫ (ihom (arNerve n)).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y)) =
      (gappedSubcomplex n C).ι ≫ (pre (arNerveMap (cutCornerOrder k x y))).app C := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => (gappedSubcomplex n C).ι ≫ f)
      (cutDiagramFamilyOperator_evaluation n k C x y))

/-- S_n 内の切断作用素の各角は端点制限の元の単体的射そのもの。 -/
lemma cutSConstructionMap_evaluation (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (x y : Fin 2) :
    cutSConstructionMap n k C ≫
      sPostcompCofiber n
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y))
        (cofiberEvaluation_preservesSConstructionData C _).toCofiberData =
      sMap C (cutCornerOrder k x y) := by
  apply (cancel_mono (gappedSubcomplex n C).ι).1
  rw [Category.assoc, sPostcompCofiber_ι, CategoryTheory.Functor.map_comp,
    ← Category.assoc, cutSConstructionMap_ι, ← Category.assoc, cutCofiberFamilyOperator_ι,
    cutRawFamilyOperator_evaluation, sMap_ι]

/-- 転置した切断 cofiber 比較も元の各角の S_n の制限を厳密に保持する。 -/
lemma cutCofiberComparison_evaluation (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (x y : Fin 2) :
    cutCofiberComparison n k C ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y) =
      sMap C (cutCornerOrder k x y) := by
  change cutSConstructionMap n k C ≫ (sCofiberComparison n C ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _) = _
  rw [sCofiberComparison_evaluation, cutSConstructionMap_evaluation]

end SerrePositivity.KST.SConstruction
