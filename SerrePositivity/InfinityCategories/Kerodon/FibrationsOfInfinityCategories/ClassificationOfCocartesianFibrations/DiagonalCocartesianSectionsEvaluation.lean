module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionsMixedCoreHom

/-!
概要：通常の反変な底上の図式と coherent な cocartesian fibration の図式の対角評価。
方針：二端点が順序を持つ場合は混合 Hom の作用を使い、逆向きは空の path から射を作る。
規約：順序の各対象で対応する相対関手空間を quasicategoryとして取る。
使われ方：Kerodon Theorem 5.6.0.2（Tag 028K）、二つの添字を同時に動かす分類関手の単体。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：反変な底上の図式と coherent な fibration の図式の同じ添字を相対 Hom で評価する。
方針：指定された射影からの相対関手空間を quasicategoryとして束縛する。
規約：通常の図式 A は順序 J の反対圏を始域とする。
使われ方：Kerodon Theorem 5.6.0.2（Tag 028K）、対角 coherent 図式の対象の作用。 -/
def diagonalCocartesianSectionsObject {B : SSet.{u}} {J : Type u} [LinearOrder J]
    (A : Jᵒᵖ ⥤ Over B)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B))
    (i : SimplicialThickening J) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsQCatObject (A.obj (Opposite.op i.as)) (F.obj i)

/-- 概要：対角評価の二対象間の豊穣 Hom の作用。
方針：順向きでは fibration の Hom を混合作用で写し、逆向きでは path の不存在を使う。
規約：順序の証明の選択は射を変えない。
使われ方：Kerodon Theorem 5.6.0.2（Tag 028K）、対角 coherent 図式の Hom の作用。 -/
noncomputable def diagonalCocartesianSectionsHom {B : SSet.{u}} {J : Type u} [LinearOrder J]
    (A : Jᵒᵖ ⥤ Over B)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B))
    (i j : SimplicialThickening J) :
    SimplicialCategory.sHom i j ⟶
      SimplicialCategory.sHom (diagonalCocartesianSectionsObject A F i)
        (diagonalCocartesianSectionsObject A F j) :=
  if h : i.as ≤ j.as then
    F.map i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsMixedCoreHom
      (A.map (homOfLE h).op) (F.obj i) (F.obj j)
  else
    { app n := ↾fun P ↦ (h (SimplicialThickening.Path.le (P.obj 0))).elim
      naturality {n m} α := by
        apply ConcreteCategory.hom_ext
        intro P
        exact (h (SimplicialThickening.Path.le (P.obj 0))).elim }

/-- 概要：端点が順方向なら対角評価の Hom は混合作用の式に一致する。
方針：順序による分岐の肯定側を計算する。
規約：h の証明は任意。
使われ方：Kerodon Theorem 5.6.0.2（Tag 028K）、対角評価の単位則と合成則の検証。 -/
lemma diagonalCocartesianSectionsHom_of_le {B : SSet.{u}} {J : Type u} [LinearOrder J]
    (A : Jᵒᵖ ⥤ Over B)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B))
    (i j : SimplicialThickening J) (h : i.as ≤ j.as) :
    diagonalCocartesianSectionsHom A F i j =
      F.map i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsMixedCoreHom
      (A.map (homOfLE h).op) (F.obj i) (F.obj j) :=
  dite_eq_left h

/-- 概要：二つの図式の対角評価は thickening から quasicategoryへの豊穣関手。
方針：順向きの Hom では混合作用の単位則・合成則を使い、空の Hom の場合を除く。
規約：底 B の充填性は不要。
使われ方：Kerodon Theorem 5.6.0.2（Tag 028K）、分類関手の二変数の単体の組立て。 -/
noncomputable def diagonalCocartesianSectionsEvaluation {B : SSet.{u}} {J : Type u} [LinearOrder J]
    (A : Jᵒᵖ ⥤ Over B)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationCategory B)) :
    EnrichedFunctor SSet.{u} (SimplicialThickening J) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} where
  obj := diagonalCocartesianSectionsObject A F
  map := diagonalCocartesianSectionsHom A F
  map_id i := by
    rw [diagonalCocartesianSectionsHom_of_le A F i i le_rfl, ← Category.assoc, F.map_id]
    have hA : A.map (homOfLE (le_refl i.as)).op = 𝟙 (A.obj (Opposite.op i.as)) := A.map_id _
    rw [hA]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsMixedCoreHom_id (A.obj (Opposite.op i.as)) (F.obj i)
  map_comp i j k := by
    by_cases hij : i.as ≤ j.as
    · by_cases hjk : j.as ≤ k.as
      · rw [diagonalCocartesianSectionsHom_of_le A F i k (hij.trans hjk),
          diagonalCocartesianSectionsHom_of_le A F i j hij,
          diagonalCocartesianSectionsHom_of_le A F j k hjk]
        rw [← Category.assoc, F.map_comp, Category.assoc]
        have hA : A.map (homOfLE (hij.trans hjk)).op =
            A.map (homOfLE hjk).op ≫ A.map (homOfLE hij).op := by
          rw [← A.map_comp]
          rfl
        change (F.map i j ⊗ₘ F.map j k) ≫
          eComp SSet (F.obj i) (F.obj j) (F.obj k) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsMixedCoreHom (A.map (homOfLE (hij.trans hjk)).op)
              (F.obj i) (F.obj k) =
          (F.map i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsMixedCoreHom (A.map (homOfLE hij).op)
              (F.obj i) (F.obj j) ⊗ₘ
            F.map j k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsMixedCoreHom (A.map (homOfLE hjk).op)
              (F.obj j) (F.obj k)) ≫
            eComp SSet (diagonalCocartesianSectionsObject A F i)
              (diagonalCocartesianSectionsObject A F j) (diagonalCocartesianSectionsObject A F k)
        rw [hA, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsMixedCoreHom_comp, tensorHom_comp_tensorHom_assoc]
        rfl
      · apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        rintro ⟨P, Q⟩
        exact (hjk (SimplicialThickening.Path.le (Q.obj 0))).elim
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      rintro ⟨P, Q⟩
      exact (hij (SimplicialThickening.Path.le (P.obj 0))).elim

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
