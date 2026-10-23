module

public import SerrePositivity.InfinityCategories.F1.Diagrams.DiagonalCocartesianSectionsEvaluation
public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionsMixedUnit
public import SerrePositivity.InfinityCategories.F1.Coherent.ConstantOrderDiagram
public import SerrePositivity.InfinityCategories.F1.Coherent.OrderDiagrams

/-!
概要：fibration のパラメーターを固定した対角相対評価の通常の図式による表示。
方針：反変な底上の図式の相対 Hom を通常の QCat 値関手とし、混合作用の単位で比較する。
規約：底の図式の対象は動かし、標的の fibration は固定する。
使われ方：Kerodon Theorem 5.6.0.2、coherent な straightening の頂点での値の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の反変図式から固定した cocartesian fibration への相対 Hom は通常の QCat 値図式をなす。
方針：底上の射による前合成を各関手空間の射とし、二つの反変性を合成する。
規約：標的の fibration p は束縛した対象。
使われ方：Kerodon Theorem 5.6.0.2、coherent な対角評価の通常の図式での表示。 -/
def cocartesianSectionsQCatDiagram {B : SSet.{u}} {J : Type u} [Category.{u} J]
    (A : Jᵒᵖ ⥤ Over B) (p : CocartesianFibrationCategory B) : J ⥤ QCat.{u} where
  obj i := cocartesianSectionsQCatObject (A.obj (Opposite.op i)) p
  map f := kanCocartesianSectionsPre p.val.hom (A.map f.op)
  map_id i := by
    rw [show A.map (𝟙 i).op = 𝟙 _ from A.map_id _, kanCocartesianSectionsPre_id]
    rfl
  map_comp f g := by
    change kanCocartesianSectionsPre p.val.hom (A.map (g.op ≫ f.op)) = _
    rw [A.map_comp, ← kanCocartesianSectionsPre_comp]
    rfl

/-- 概要：定値な fibration の図式による対角評価は相対 Hom の通常の関手の coherent 表示に一致する。
方針：各 Hom の単体で順序を取り出し、恒等射における混合作用を通常の前合成へ戻す。
規約：J は任意の線形順序。局所 Kan 性を追加の仮定にしない。
使われ方：Kerodon Theorem 5.6.0.2、分類関手を fibration の頂点で評価する計算。 -/
lemma diagonalCocartesianSectionsEvaluation_constant {B : SSet.{u}} {J : Type u} [LinearOrder J]
    (A : Jᵒᵖ ⥤ Over B) (p : CocartesianFibrationCategory B) :
    diagonalCocartesianSectionsEvaluation A (enrichedConstantOrderDiagram J p) =
      enrichedFunctorOfOrderDiagram (cocartesianSectionsQCatDiagram A p) := by
  refine EnrichedFunctor.ext SSet
    (F := diagonalCocartesianSectionsEvaluation A (enrichedConstantOrderDiagram J p))
    (G := enrichedFunctorOfOrderDiagram (cocartesianSectionsQCatDiagram A p)) (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  have hij : i.as ≤ j.as := SimplicialThickening.Path.le (P.obj 0)
  change (diagonalCocartesianSectionsHom A (enrichedConstantOrderDiagram J p) i j).app d P = _
  erw [diagonalCocartesianSectionsHom_of_le A (enrichedConstantOrderDiagram J p) i j hij]
  change ((toUnit _ ≫ eId SSet p ≫
    cocartesianSectionsMixedCoreHom (A.map (homOfLE hij).op) p p).app d) P =
    PinchedHom.constant
      (SimplicialCategory.homEquiv'
        (cocartesianSectionsQCatObject (A.obj (Opposite.op i.as)) p)
        (cocartesianSectionsQCatObject (A.obj (Opposite.op j.as)) p)
        (show cocartesianSectionsQCatObject (A.obj (Opposite.op i.as)) p ⟶
          cocartesianSectionsQCatObject (A.obj (Opposite.op j.as)) p from
            kanCocartesianSectionsPre p.val.hom (A.map (homOfLE hij).op))) d.unop.len
  erw [cocartesianSectionsMixedCoreHom_unit]
  exact unitHom_app_constant (eHomEquiv SSet
    (show cocartesianSectionsQCatObject (A.obj (Opposite.op i.as)) p ⟶
      cocartesianSectionsQCatObject (A.obj (Opposite.op j.as)) p from
        kanCocartesianSectionsPre p.val.hom (A.map (homOfLE hij).op))) d.unop.len

end SerrePositivity.InfinityCategories
