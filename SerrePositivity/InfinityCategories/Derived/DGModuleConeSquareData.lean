module
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareData
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeSquare

/-! # 標準 cone 四角形の全 Hom end データ

概要：標準 cone 四角形の四辺・対角・二つの次数 −1 成分を明示する。
方針：閉零の cone 包含と次数 −1 の左包含を使い、二つの実三角形を同定する。
規約：零角は具体的な零加群。使われ方：dg 関手による標準 cofiber 四角形の像。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 標準 cone 四角形の四辺と全 dg 自然なホモトピーデータ。 -/
def dgModuleConeSquareData (f : M ⟶ N) :
    DGModuleSquareData A D M N (moduleZero A D) (moduleCone A D f) where
  bottom := f
  left := 0
  right := moduleConeInr A D f
  top := 0
  diagonal := 0
  lowerHomotopy := moduleConeInlElement A D f
  upperHomotopy := 0
  lowerEquation := by
    change _ = _ - 0
    rw [sub_zero]
    exact moduleConeInlElement_d A D f
  upperEquation := by
    rw [zero_comp, sub_self]
    exact map_zero _

/-- データから貼った実四角形は既存の標準 cone 四角形。 -/
lemma dgModuleConeSquareData_square (f : M ⟶ N) :
    (dgModuleConeSquareData A D f).square = dgModuleConeSquare A D f := by
  apply square_isPushout.hom_ext
  · rw [DGModuleSquareData.square_upper, dgModuleConeSquare_upper]
    rfl
  · rw [DGModuleSquareData.square_lower, dgModuleConeSquare_lower]
    rfl

end SerrePositivity.InfinityCategories
