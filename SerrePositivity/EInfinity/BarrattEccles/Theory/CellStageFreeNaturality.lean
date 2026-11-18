module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageGradedBasis

/-!
# 元の生成元の自由表示とセル段の包含

## 概要
Berger–Moerdijk 命題 4.1 のセル段の自由表示を、後の段への指定射と比較する。

## 方針
球複体の余積の指定包含で微分消去の比較を確認し、自由代数の自然同型を合成する。

## 規約
自由代数の生成元は微分を消す前の球複体の余積を使う。

## 使われ方
後のセル段への包含で語の重みが増えないことの証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Operad
open CategoryTheory Limits HomologicalComplex HomotopicalAlgebra DifferentialGraded
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : P.Algebra} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u}
    (fun (_ : J) n => P.freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- The original generator coproduct map from one stage to a later stage. -/
def cellStageGeneratorCoproductMap {j k : J} (h : j ≤ k) :
    (∐ (cellStageGeneratorSpheres c j)) ⟶ ∐ (cellStageGeneratorSpheres c k) :=
  Sigma.desc (fun x => Sigma.ι (cellStageGeneratorSpheres c k)
    (cellsBeforeInclusion (CellsAt c) h x))

/-- The erasure/coproduct comparison preserves each specified generator inclusion. -/
@[reassoc]
lemma cellStageErasedGeneratorsIso_ι (j : J) (x : CellsBefore (CellsAt c) j) :
    (eraseDifferential A).map (Sigma.ι (cellStageGeneratorSpheres c j) x) ≫
      (cellStageErasedGeneratorsIso c j).hom =
      Sigma.ι (fun y : CellsBefore (CellsAt c) j => cellSphere c y.1 y.2) x := by
  let E := eraseDifferential A
  let V := cellStageGeneratorSpheres c j
  let h := isColimitCofanMkObjOfIsColimit E V (Sigma.ι V)
    (colimit.isColimit (Discrete.functor V))
  exact IsColimit.comp_coconePointUniqueUpToIso_hom h
    (colimit.isColimit (Discrete.functor _)) (Discrete.mk x)

/-- The erasure/coproduct comparison is natural for the original generator maps. -/
lemma cellStageErasedGeneratorsIso_naturality {j k : J} (h : j ≤ k) :
    (eraseDifferential A).map (cellStageGeneratorCoproductMap c h) ≫
      (cellStageErasedGeneratorsIso c k).hom =
      (cellStageErasedGeneratorsIso c j).hom ≫ cellSphereCoproductMap c h := by
  let E := eraseDifferential A
  let V := cellStageGeneratorSpheres c j
  let hV := isColimitCofanMkObjOfIsColimit E V (Sigma.ι V)
    (colimit.isColimit (Discrete.functor V))
  apply Cofan.IsColimit.hom_ext hV
  intro x
  change (eraseDifferential A).map (Sigma.ι (cellStageGeneratorSpheres c j) x) ≫
      (eraseDifferential A).map (cellStageGeneratorCoproductMap c h) ≫
        (cellStageErasedGeneratorsIso c k).hom =
    (eraseDifferential A).map (Sigma.ι (cellStageGeneratorSpheres c j) x) ≫
      (cellStageErasedGeneratorsIso c j).hom ≫ cellSphereCoproductMap c h
  rw [← CategoryTheory.Functor.map_comp_assoc, cellStageGeneratorCoproductMap,
    Sigma.ι_comp_desc, cellStageErasedGeneratorsIso_ι,
    cellStageErasedGeneratorsIso_ι_assoc, cellSphereCoproductMap, Sigma.ι_comp_desc]

/-- The inverse comparison is natural for the same generator maps. -/
lemma cellStageErasedGeneratorsIso_inv_naturality {j k : J} (h : j ≤ k) :
    cellSphereCoproductMap c h ≫ (cellStageErasedGeneratorsIso c k).inv =
      (cellStageErasedGeneratorsIso c j).inv ≫
        (eraseDifferential A).map (cellStageGeneratorCoproductMap c h) := by
  have he := congrArg (fun z => (cellStageErasedGeneratorsIso c j).inv ≫ z ≫
    (cellStageErasedGeneratorsIso c k).inv) (cellStageErasedGeneratorsIso_naturality c h)
  simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc,
    Category.comp_id] at he
  exact he.symm

/-- The original-free-algebra stage comparison is natural for actual stage maps. -/
lemma cellStageErasedFreeIso_naturality (hX : IsInitial X) {j k : J} (h : j ≤ k) :
    P.eraseAlgebra.map (c.F.map (homOfLE h)) ≫ (cellStageErasedFreeIso c hX k).hom =
      (cellStageErasedFreeIso c hX j).hom ≫
        P.eraseAlgebra.map (P.freeAlgebraFunctor.map (cellStageGeneratorCoproductMap c h)) := by
  let F := P.erase.freeAlgebraFunctor
  let g := cellStageGeneratorCoproductMap c h
  have hn := P.eraseFreeAlgebraIso.inv.naturality g
  change F.map ((eraseDifferential A).map g) ≫
      (P.eraseFreeAlgebraIso.inv.app (∐ (cellStageGeneratorSpheres c k))) =
    (P.eraseFreeAlgebraIso.inv.app (∐ (cellStageGeneratorSpheres c j))) ≫
      P.eraseAlgebra.map (P.freeAlgebraFunctor.map g) at hn
  simp only [cellStageErasedFreeIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% (erasedCellStageFreeIso_naturality c hX h)]
  rw [← CategoryTheory.Functor.map_comp_assoc,
    cellStageErasedGeneratorsIso_inv_naturality, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  erw [hn]
  rfl

end SerrePositivity.EInfinity.Operad
