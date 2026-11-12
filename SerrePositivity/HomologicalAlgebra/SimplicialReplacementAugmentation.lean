module

public import SerrePositivity.HomologicalAlgebra.SimplicialReplacement
import all SerrePositivity.HomologicalAlgebra.SimplicialReplacement

/-!
# 厳密な余錐が指定する単体的置換の増大

## 概要
元の図式の厳密な余錐から、各射列の先頭の脚を使う同じ単体的置換の増大を作る。

## 方針
各余積因子で元の余錐の脚を使い、単体作用素との両立を余錐の自然性で示す。

## 規約
同じ余錐の頂点と脚を保持する。native な余錐の存在や普遍性は仮定しない。

## 使われ方
Weibel §2.2、HA 1.2.4。bar の線形重みの同じ増大と射影分解の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.HomologicalAlgebra
variable {J : Type} [SmallCategory J]
variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C]

/-- 厳密な余錐の同じ脚を余積の各因子に用いた、単体的置換の増大。 -/
def replacementCoconeAugmentation {F : J ⥤ C} (c : Cocone F) :
    simplicialReplacement F ⟶ (SimplicialObject.const C).obj c.pt where
  app n := Sigma.desc (fun s => c.ι.app (s.obj 0))
  naturality {n m} r := by
    apply Sigma.hom_ext
    intro s
    change Sigma.ι (replacementTerms F n) s ≫ (replacementMap F r ≫ _) = _
    rw [ι_replacementMap_assoc]
    simp only [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    exact c.ι.naturality (s.map (homOfLE (Fin.zero_le (r.unop.toOrderHom 0))))

/-- 同じ厳密な余錐が指定する、増大単体的置換。 -/
def replacementCoconeAugmented {F : J ⥤ C} (c : Cocone F) :
    SimplicialObject.Augmented C where
  left := simplicialReplacement F
  right := c.pt
  hom := replacementCoconeAugmentation c

/-- 増大の各因子上の射は、元の同じ余錐の先頭の脚。 -/
@[reassoc (attr := simp)]
theorem ι_replacementCoconeAugmentation {F : J ⥤ C} (c : Cocone F)
    (n : SimplexCategoryᵒᵖ) (s : ComposableArrows J n.unop.len) :
    Sigma.ι (replacementTerms F n) s ≫ (replacementCoconeAugmentation c).app n =
      c.ι.app (s.obj 0) := Sigma.ι_comp_desc _ _

end SerrePositivity.HomologicalAlgebra
