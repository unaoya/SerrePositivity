module
public import SerrePositivity.KST.SConstruction.CoherentDiagramFamilyPasting
public import SerrePositivity.KST.SConstruction.AssemblyCoherentFactorLegs

/-! # 組み立ての全選択空間にわたる二脚の貼り合わせ
概要：延長・逆射の全選択を同時に動かして、元の混合空間内の二脚を貼る。
方針：入力射の恒等両端からの cospan に普遍 over 族の貼り合わせを適用する。
規約：入力射ごとの全パラメーターを保つ。異なる入力射間の高次整合性は別工程。
使われ方：スペクトル構造射の coherent な自然性の因子比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 延長の全 coherent 選択にわたって二脚を貼るための全選択空間。 -/
def kanAssemblyCoherentPastingChoices {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y) : SSet.{u} :=
  diagramUniversalCospanPastingChoices (kanAssemblyInputArrowDiagram r F)
    (assemblyArrowFromSource f) (assemblyArrowFromTarget f)

/-- 逆射の全 coherent 選択にわたって二脚を貼るための全選択空間。 -/
def oneDirectionInverseCoherentPastingChoices {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y) : SSet.{u} :=
  diagramUniversalCospanPastingChoices (oneDirectionInverseInputArrowDiagram r F)
    (assemblyArrowFromSource f) (assemblyArrowFromTarget f)

/-- 延長の全選択にわたる貼り合わせの選択空間は可縮 Kan。 -/
lemma kanAssemblyCoherentPastingChoices_isContractibleKan {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (kanAssemblyCoherentPastingChoices r F f) := by
  let : KanComplex ((kanAssemblyInputArrowDiagram r F).obj (assemblyArrowMk f)) :=
    (kanAssemblyInputArrowDiagram_isContractibleKan r F (assemblyArrowMk f)).kanComplex
  exact diagramUniversalCospanPastingChoices_isContractibleKan _ _ _

/-- 逆射の全選択にわたる貼り合わせの選択空間は可縮 Kan。 -/
lemma oneDirectionInverseCoherentPastingChoices_isContractibleKan
    {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
    {X Y : I} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (oneDirectionInverseCoherentPastingChoices r F f) := by
  let : KanComplex ((oneDirectionInverseInputArrowDiagram r F).obj (assemblyArrowMk f)) :=
    (oneDirectionInverseInputArrowDiagram_isContractibleKan r F (assemblyArrowMk f)).kanComplex
  exact diagramUniversalCospanPastingChoices_isContractibleKan _ _ _

/-- 全 coherent 延長選択を同時に動かす、元の混合空間内の実三角形の族。 -/
def kanAssemblyCoherentPastingFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y)
    (v : (kanAssemblyCoherentPastingChoices r F f) _⦋0⦌) :=
  diagramUniversalCospanPastingFamily (kanAssemblyInputArrowDiagram r F)
    (assemblyArrowFromSource f) (assemblyArrowFromTarget f) v

/-- 全 coherent 逆射選択を同時に動かす、元の混合空間内の実三角形の族。 -/
def oneDirectionInverseCoherentPastingFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y)
    (v : (oneDirectionInverseCoherentPastingChoices r F f) _⦋0⦌) :=
  diagramUniversalCospanPastingFamily (oneDirectionInverseInputArrowDiagram r F)
    (assemblyArrowFromSource f) (assemblyArrowFromTarget f) v

/-- 延長の普遍的な貼り合わせを、既存の任意の高次部分を保って補完できる。 -/
lemma kanAssemblyCoherentPastingChoices_relative_lifting {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y)
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j]
    (a : S ⟶ kanAssemblyCoherentPastingChoices r F f) :
    ∃ b : T ⟶ kanAssemblyCoherentPastingChoices r F f, j ≫ b = a := by
  let : KanComplex ((kanAssemblyInputArrowDiagram r F).obj (assemblyArrowMk f)) :=
    (kanAssemblyInputArrowDiagram_isContractibleKan r F (assemblyArrowMk f)).kanComplex
  exact diagramUniversalCospanPastingChoices_relative_lifting _ _ _ j a

/-- 逆射の普遍的な貼り合わせを、既存の任意の高次部分を保って補完できる。 -/
lemma oneDirectionInverseCoherentPastingChoices_relative_lifting
    {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
    {X Y : I} (f : X ⟶ Y) {S T : SSet.{u}} (j : S ⟶ T) [Mono j]
    (a : S ⟶ oneDirectionInverseCoherentPastingChoices r F f) :
    ∃ b : T ⟶ oneDirectionInverseCoherentPastingChoices r F f, j ≫ b = a := by
  let : KanComplex ((oneDirectionInverseInputArrowDiagram r F).obj (assemblyArrowMk f)) :=
    (oneDirectionInverseInputArrowDiagram_isContractibleKan r F (assemblyArrowMk f)).kanComplex
  exact diagramUniversalCospanPastingChoices_relative_lifting _ _ _ j a

/-- 全 coherent 選択にわたり、同じ二脚を貼って得るEdge。 -/
def kanAssemblyCoherentPastedEdge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y)
    (v : (kanAssemblyCoherentPastingChoices r F f) _⦋0⦌) :=
  diagramUniversalCospanPastedEdge (kanAssemblyInputArrowDiagram r F)
    (assemblyArrowFromSource f) (assemblyArrowFromTarget f) v

/-- 全 coherent 選択にわたり、同じ二脚を貼って得るTriangle。 -/
def kanAssemblyCoherentPastedTriangle {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y)
    (v : (kanAssemblyCoherentPastingChoices r F f) _⦋0⦌) :=
  diagramUniversalCospanPastedTriangle (kanAssemblyInputArrowDiagram r F)
    (assemblyArrowFromSource f) (assemblyArrowFromTarget f) v

/-- 全 coherent 選択にわたり、同じ二脚を貼って得るEdge。 -/
def oneDirectionInverseCoherentPastedEdge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y)
    (v : (oneDirectionInverseCoherentPastingChoices r F f) _⦋0⦌) :=
  diagramUniversalCospanPastedEdge (oneDirectionInverseInputArrowDiagram r F)
    (assemblyArrowFromSource f) (assemblyArrowFromTarget f) v

/-- 全 coherent 選択にわたり、同じ二脚を貼って得るTriangle。 -/
def oneDirectionInverseCoherentPastedTriangle {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {X Y : I} (f : X ⟶ Y)
    (v : (oneDirectionInverseCoherentPastingChoices r F f) _⦋0⦌) :=
  diagramUniversalCospanPastedTriangle (oneDirectionInverseInputArrowDiagram r F)
    (assemblyArrowFromSource f) (assemblyArrowFromTarget f) v

end SerrePositivity.KST.SConstruction
