module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomComparisonLimit
public import SerrePositivity.InfinityCategories.F2.Presentable.FullyFaithfulHomComparison
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.CoconeVertex

/-!
概要：反対前層圏の自然変換の可逆性を元の Yoneda 像上で検出する。
方針：前層の全密度余錐を反転し、同じ極限錐上で成分の可逆性を延長する。
規約：両関手が保存する密度錐を明示し、表現可能性を仮定しない。
使われ方：小余極限を小極限へ送る前層の表現可能性の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open Ind

/-- 概要：反対密度錐を保つ二関手の比較は Yoneda 像上で可逆なら全体で可逆。
方針：各前層を同じ密度錐の頂点として回収し、比較の極限閉性を適用する。
規約：任意の全自然変換と全 coherent な密度図式を扱う。
使われ方：制限上の比較から前層全体の表現同型を構成する。 -/
lemma presheafOpposite_functorHom_isIso_of_yoneda
    {A : SSet.{u}} [Quasicategory A] {E : SSet.{u + 1}} [Quasicategory E]
    {F G : (PresheafInfinity A).op ⟶ E} (t : FunctorHom F G)
    (hF : ∀ P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u},
      IsLimitCone (mapJoinCone F (F1B.coconeReverseCone (presheafDensityCocone P))))
    (hG : ∀ P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u},
      IsLimitCone (mapJoinCone G (F1B.coconeReverseCone (presheafDensityCocone P))))
    (ht : ∀ a : A _⦋0⦌, IsIso ((hoFunctor.map (evaluateFunctorAt (Y := E)
      (SSet.opObjEquiv.symm (functorVertex (representablePresheafInfinity a))))).toFunctor.map t)) :
    IsIso t := by
  apply functorHom_isIso_of_components
  intro v
  obtain ⟨P, hP⟩ := (presheafInfinityObjectEquiv A).surjective (SSet.opObjEquiv v)
  change functorVertex P = SSet.opObjEquiv v at hP
  have h := functorHomComparison_limit_vertex
    (F1B.coconeReverseCone (presheafDensityCocone P)) t (hF P) (hG P) (by
      intro j
      let a := (smallRightUnstraighteningProjection P).app (Opposite.op ⦋0⦌)
        (SSet.opObjEquiv j).down
      have hv : (SSet.opFunctor.map (presheafElementsYonedaDiagram P)).app
          (Opposite.op ⦋0⦌) j =
            SSet.opObjEquiv.symm (functorVertex (representablePresheafInfinity a)) := by
        change SSet.opObjEquiv.symm ((presheafElementsYonedaDiagram P).app
          (Opposite.op ⦋0⦌) (SSet.opObjEquiv j)) = _
        exact congrArg (SSet.opObjEquiv (X := PresheafInfinity A)).symm
          (presheafElementsYonedaDiagram_vertex P (SSet.opObjEquiv j).down)
      rw [hv]
      exact ht a)
  rw [F1B.coconeReverseCone_vertex, presheafDensityCocone_vertex, hP] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable
