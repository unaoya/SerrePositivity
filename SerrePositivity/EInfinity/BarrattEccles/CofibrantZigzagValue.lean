module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.ULiftRelativeLocalizationValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueNaturality
public import SerrePositivity.EInfinity.BarrattEccles.DKMappingComponents

/-!
# 元の cofibrant 包含と通常の局所化同値による全語の値

概要：native DK 入力の同じ全 zigzag の包含後の値を回収する。
方針：元の down の Hom 同値と包含の因子化自然同型を使う。
規約：元の cofibrant 対象・包含・選ばれた局所化同値を保持する。
使われ方：既存 DK/Map^h π₀ 同値と元の高次比較の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.HomotopicalAlgebra
variable (A : Type u) [CommRing A]

def cofibrantAlgebraDKHoHomMap (X Y : CofibrantAlgebra A)
    (f : (cofibrantAlgebraRelativeCategory A).weakEquivalences.Q.obj
        (cofibrantAlgebraDKObject A X) ⟶
      (cofibrantAlgebraRelativeCategory A).weakEquivalences.Q.obj (cofibrantAlgebraDKObject A Y)) :
    let := modelCategory A
    (weakEquivalences (operad A).Algebra).Q.obj ((cofibrantAlgebraInclusion A).obj X) ⟶
      (weakEquivalences (operad A).Algebra).Q.obj ((cofibrantAlgebraInclusion A).obj Y) := by
  let := modelCategory A
  let i := cofibrantAlgebraInclusionLocalizedIso A
  exact (i.app X).hom ≫ (cofibrantAlgebraHoEquivalence A).functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.homEquiv (cofibrantAlgebraWeakEquivalences A) _ _ f) ≫
      (i.app Y).inv

lemma cofibrantAlgebraZigzagValue_inclusion (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : CofibrantAlgebra A)
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (cofibrantAlgebraRelativeCategory A).weakEquivalences w
      (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y)) :
    let := modelCategory A
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value (weakEquivalences (operad A).Algebra).Q
        (weakEquivalences (operad A).Algebra).Q_inverts
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj (cofibrantAlgebraDKInclusionRelative A) S) =
      cofibrantAlgebraDKHoHomMap A X Y
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value (cofibrantAlgebraRelativeCategory A).weakEquivalences.Q
          (cofibrantAlgebraRelativeCategory A).weakEquivalences.Q_inverts S) := by
  let := modelCategory A
  let Q := (weakEquivalences (operad A).Algebra).Q
  let R := (cofibrantAlgebraWeakEquivalences A).Q
  let E := cofibrantAlgebraHoEquivalence A
  let i := cofibrantAlgebraInclusionLocalizedIso A
  let D := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.down (cofibrantAlgebraWeakEquivalences A)
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj D S
  let F := cofibrantAlgebraInclusionRelative A
  have hT : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value Q (weakEquivalences (operad A).Algebra).Q_inverts
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj (cofibrantAlgebraDKInclusionRelative A) S) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value (F.functor ⋙ Q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.relativeInverts F Q (weakEquivalences (operad A).Algebra).Q_inverts) T :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_relative F Q (weakEquivalences (operad A).Algebra).Q_inverts T
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_naturality
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.relativeInverts F Q (weakEquivalences (operad A).Algebra).Q_inverts)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postInverts R (cofibrantAlgebraWeakEquivalences A).Q_inverts E.functor) i.hom T
  have hd := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homEquiv_value
    (cofibrantAlgebraWeakEquivalences A) w
    (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y) S
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_postcompose R
    (cofibrantAlgebraWeakEquivalences A).Q_inverts E.functor T
  change _ = (i.app X).hom ≫ E.functor.map _ ≫ (i.app Y).inv
  apply (cancel_mono (i.app Y).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (congrArg (fun k => k ≫ (i.app Y).hom) hT).trans
    (hn.trans ((congrArg (fun k => (i.app X).hom ≫ k) hv).trans
      (congrArg (fun k => (i.app X).hom ≫ E.functor.map k) hd.symm)))

end SerrePositivity.EInfinity.BarrattEccles
