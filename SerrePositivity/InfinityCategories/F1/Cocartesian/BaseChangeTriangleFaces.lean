module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleFamily
public import SerrePositivity.InfinityCategories.F1.QCatDiagramTriangleFaces

/-!
概要：元の共同実現の二単体の三面は、元の底変換比較の同じ三辺。
方針：元の三点図式の coherent な二単体の面を、豊穣三角形の同じ成分へ戻す。
規約：全 fibration の実現から得た同じ二単体を使う。
使われ方：元の Hom 比較 span の結合と Segal 制限の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p : CocartesianFibrationCategory (nerve C)) (a : A)

/-- 共同実現の同じ二単体の最初の辺は、元の最初の底変換比較。 -/
lemma cocartesianBaseChangeTriangleSimplex_first :
    CatInfinity.δ (2 : Fin 3) (cocartesianBaseChangeTriangleSimplex l k p a) =
      (coherentNerveEdge
        ((cocartesianStrictTransportBaseChangeQCat p.val.hom k).app (l.obj a))).edge := by
  rw [cocartesianBaseChangeTriangleSimplex_eq, qCatDiagramCoherentNerve_triangle_first]
  have hm : (quasicategoryDiagramValueFunctor
      ((cocartesianBaseChangeTriangle l k).toCoreEnrichedFunctor.obj p)).map
      ((homOfLE (show (0 : Fin 3) ≤ 1 by decide), 𝟙 a) :
        ((0 : Fin 3), a) ⟶ ((1 : Fin 3), a)) =
      (cocartesianStrictTransportBaseChangeQCat p.val.hom k).app (l.obj a) :=
    cocartesianBaseChangeTriangle_first l k a p
  exact congrArg (fun f ↦ (coherentNerveEdge f).edge) hm

/-- 共同実現の同じ二単体の次の辺は、二回目の元の比較に結合同型を合成した辺。 -/
lemma cocartesianBaseChangeTriangleSimplex_second :
    CatInfinity.δ (0 : Fin 3) (cocartesianBaseChangeTriangleSimplex l k p a) =
      (coherentNerveEdge
        ((cocartesianStrictTransportBaseChangeQCat (pullback.fst (nerveMap k) p.val.hom) l).app a ≫
          (cocartesianBaseChangeAssociativityQCat p.val.hom l k).app a)).edge := by
  rw [cocartesianBaseChangeTriangleSimplex_eq, qCatDiagramCoherentNerve_triangle_second]
  have hm : (quasicategoryDiagramValueFunctor
      ((cocartesianBaseChangeTriangle l k).toCoreEnrichedFunctor.obj p)).map
      ((homOfLE (show (1 : Fin 3) ≤ 2 by decide), 𝟙 a) :
        ((1 : Fin 3), a) ⟶ ((2 : Fin 3), a)) =
      (cocartesianStrictTransportBaseChangeQCat (pullback.fst (nerveMap k) p.val.hom) l).app a ≫
        (cocartesianBaseChangeAssociativityQCat p.val.hom l k).app a :=
    cocartesianBaseChangeTriangle_second l k a p
  exact congrArg (fun f ↦ (coherentNerveEdge f).edge) hm

/-- 共同実現の同じ二単体の長辺は、元の直接の底変換比較そのもの。 -/
lemma cocartesianBaseChangeTriangleSimplex_long :
    CatInfinity.δ (1 : Fin 3) (cocartesianBaseChangeTriangleSimplex l k p a) =
      (coherentNerveEdge ((cocartesianStrictTransportBaseChangeQCat p.val.hom (l ⋙ k)).app a)).edge := by
  rw [cocartesianBaseChangeTriangleSimplex_eq, qCatDiagramCoherentNerve_triangle_long]
  have he :
      CategoryStruct.comp (obj := Fin 3 × A)
        (X := ((0 : Fin 3), a)) (Y := ((1 : Fin 3), a)) (Z := ((2 : Fin 3), a))
      ((homOfLE (show (0 : Fin 3) ≤ 1 by decide), 𝟙 a) :
        ((0 : Fin 3), a) ⟶ ((1 : Fin 3), a))
      ((homOfLE (show (1 : Fin 3) ≤ 2 by decide), 𝟙 a) :
        ((1 : Fin 3), a) ⟶ ((2 : Fin 3), a)) =
      ((homOfLE (show (0 : Fin 3) ≤ 2 by decide), 𝟙 a) :
        ((0 : Fin 3), a) ⟶ ((2 : Fin 3), a)) := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact Category.id_comp _
  rw [he]
  have hm : (quasicategoryDiagramValueFunctor
      ((cocartesianBaseChangeTriangle l k).toCoreEnrichedFunctor.obj p)).map
      ((homOfLE (show (0 : Fin 3) ≤ 2 by decide), 𝟙 a) :
        ((0 : Fin 3), a) ⟶ ((2 : Fin 3), a)) =
      (cocartesianStrictTransportBaseChangeQCat p.val.hom (l ⋙ k)).app a :=
    cocartesianBaseChangeTriangle_long l k a p
  exact congrArg (fun f ↦ (coherentNerveEdge f).edge) hm

end SerrePositivity.InfinityCategories
