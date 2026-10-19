module

public import SerrePositivity.InfinityCategories.F1.CoherentCompositionReverse
public import SerrePositivity.InfinityCategories.F1.KanPointHomActionIso
public import SerrePositivity.InfinityCategories.F1.OppositeInternalHomEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseInternalHom

/-!
概要：反対の Kan 圏における一点 Hom の反転合成作用を内部 Hom の同型として表示する。
方針：合成作用を curry し、ULift と反転の内部 Hom 比較へ分解する。
規約：実際の coherentReverseHomComposition の作用を扱う。
使われ方：普遍 coslice 輸送の写像空間上の同値性への標準作用側の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：反対 Kan 圏の一点 Hom の反転合成は標準作用と ULift・反転比較の合成。
方針：展開して二つの内部 Hom 比較の評価公式を使い、残る直積の交換を計算する。
規約：写像空間と係数の宇宙は coherent nerve に合わせて持ち上げる。
使われ方：標準反転合成作用の同型性。 -/
lemma coherentReversePointHomAction_eq (K L : KanObject.{u}) :
    curry (coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
      (Opposite.op pointKanObject)) =
    SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map (kanPointHomEnriched.map K L)) ≫
      SSet.opFunctor.map (HomotopyLimits.uliftInternalHomComparison
        (SimplicialCategory.sHom pointKanObject K) (SimplicialCategory.sHom pointKanObject L)) ≫
      (HomotopyLimits.oppositeInternalHomIso
        ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject K))
        ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject L))).hom := by
  apply uncurry_injective
  rw [uncurry_curry, ← Category.assoc, ← SSet.opFunctor.map_comp,
    oppositeInternalHom_map_uncurry]
  have hu := HomotopyLimits.uliftInternalHomComparison_map_uncurry.{u, u + 1}
    (K := SimplicialCategory.sHom pointKanObject K)
    (B := SimplicialCategory.sHom pointKanObject L)
    (show SimplicialCategory.sHom K L ⟶
      (ihom (SimplicialCategory.sHom pointKanObject K)).obj
        (SimplicialCategory.sHom pointKanObject L) from kanPointHomEnriched.map K L)
  calc
    _ = (opTensorIso
        ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject K))
        ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))).hom ≫
      SSet.opFunctor.map ((HomotopyLimits.uliftTensorIso _ _).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (uncurry (kanPointHomEnriched.map K L))) := by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := congrArg (fun f ↦ (opTensorIso _ _).hom ≫ SSet.opFunctor.map f) hu.symm

/-- 概要：反転した一点 Hom の豊穣合成の curry は厳密な同型。
方針：一点 Hom の標準作用と ULift・反転の同型の合成へ移す。
規約：元の合成作用そのものについての同型性。
使われ方：標準輸送の作用が普遍輸送の同値性を検出する。 -/
instance coherentReversePointHomAction_isIso (K L : KanObject.{u}) :
    IsIso (curry (coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
      (Opposite.op pointKanObject))) := by
  rw [coherentReversePointHomAction_eq]
  infer_instance

end SerrePositivity.InfinityCategories
