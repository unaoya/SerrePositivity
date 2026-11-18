module

public import SerrePositivity.InfinityCategories.Sheaves.CechCommaLocalContraction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.QCatEquivalence
public import SerrePositivity.InfinityCategories.HTT.Section5_1_4.WeakContractibleOpposite
public import SerrePositivity.InfinityCategories.HTT.Section6_1_2.OppositeIso
public import Mathlib.CategoryTheory.Elements

/-!
概要：Čech 図式の同じ Hom 値の元の圏を、構成済みの comma の収縮に接続する。
方針：単体の次数と元の射を同じまま取り出し、反対圏と小さい模型だけを移送する。
規約：HTT 4.1.3.1、Kerodon Theorem 7.2.3.1（Tag 02NY）の既存の収縮の表示の法則。
使われ方：S8 の Čech 増大の各点。根はこの評価だけで使い、大域の自然な根を要求しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.HTT.Section6_1_2
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [Category.{v} C] {U V : C}

/-- 元の Čech 図式を Hom で評価し、添字だけを同じ小さい宇宙へ移す。 -/
abbrev cechPointDiagram (d : CategoryTheory.CechNerveData U) (V : C) :
    AsSmall.{v} SimplexCategoryᵒᵖ ⥤ Type v :=
  AsSmall.down ⋙ d.obj ⋙ coyoneda.obj (Opposite.op V)

/-- 反対要素圏の同じ次数と射を、元の小さい comma へ戻す。 -/
def cechPointElementsToComma (d : CategoryTheory.CechNerveData U) (V : C) :
    (cechPointDiagram d V).Elementsᵒᵖ ⥤ CechCommaLocal d V where
  obj a := AsSmall.up.obj (CostructuredArrow.mk (Y := (AsSmall.down.obj a.unop.obj).unop) a.unop.val.op)
  map f := AsSmall.up.map (CostructuredArrow.homMk (AsSmall.down.map f.unop.hom).unop (by
    apply Quiver.Hom.unop_inj
    exact f.unop.map_val))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 元の comma の次数と射から、同じ Hom の元を復元する。 -/
def cechPointElementsFromComma (d : CategoryTheory.CechNerveData U) (V : C) :
    CechCommaLocal d V ⥤ (cechPointDiagram d V).Elementsᵒᵖ where
  obj a := Opposite.op ((cechPointDiagram d V).elementsMk
    (ULift.up (Opposite.op (AsSmall.down.obj a).left)) (AsSmall.down.obj a).hom.unop)
  map f := (Functor.Elements.homMk (ULift.up (AsSmall.down.map f).left.op) (by
    exact congrArg Quiver.Hom.unop (CostructuredArrow.w (AsSmall.down.map f)))).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 指定 Hom の要素圏と既存の comma の表示は、同じ全対象・全作用素で順逆。 -/
def cechPointElementsCommaEquivalence (d : CategoryTheory.CechNerveData U) (V : C) :
    (cechPointDiagram d V).Elementsᵒᵖ ≌ CechCommaLocal d V :=
  CategoryTheory.Equivalence.mk (cechPointElementsToComma d V) (cechPointElementsFromComma d V)
    (eqToIso (by rfl)) (eqToIso (by rfl))

/-- 同じ評価の根一本から、元の Hom 値図式の要素圏の nerve の弱可縮性を得る。 -/
lemma cechPointElements_isWeaklyContractible (d : CategoryTheory.CechNerveData U)
    (r : V ⟶ U) : IsWeaklyContractible (nerve (cechPointDiagram d V).Elements) := by
  have h := (nerveQCatEquivalence (cechPointElementsCommaEquivalence d V)).isQCatEquivalence
    |>.isWeakHomotopyEquivalence.weaklyContractible_iff.mpr
      (cechCommaLocal_isWeaklyContractible d r)
  have h' := (qCatEquivalenceOfIso (nerveOppositeIso (cechPointDiagram d V).Elements)).isQCatEquivalence.isWeakHomotopyEquivalence.weaklyContractible_iff.mp h
  exact SerrePositivity.InfinityCategories.HTT.Section5_1_4.isWeaklyContractible_of_op h'

end SerrePositivity.InfinityCategories.Sheaves
