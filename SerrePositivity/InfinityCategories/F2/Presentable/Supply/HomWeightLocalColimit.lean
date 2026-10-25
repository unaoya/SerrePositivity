module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.HomWeightElementsComparison
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensity
public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentCoconeRestriction
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeValEquality

/-!
概要：任意の関手の局所左 Kan 形状上の Yoneda 図式に、元の Hom 前層を頂点とする余極限を作る。
方針：元の Hom 前層の密度余錐を、射影を厳密に保つ比較同値で制限する。
規約：指定単位から誘導される余錐との比較は別工程。
使われ方：P-12 の Hom 係数族の左 Kan 普遍性を点ごとの密度へ還元する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

local instance {A C : SSet.{u}} [Quasicategory C] (F : A ⟶ C) (c : C _⦋0⦌) :
    RightFibration (leftKanProjection F c) :=
  ⟨rightFibrations.pullback_fst _ _ (RightFibration.mem (p :=
    sliceOverProjection (SSet.yonedaEquiv.symm c)))⟩

local instance {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) : Quasicategory (leftKanShape F c) :=
  quasicategory_of_innerFibration (leftKanProjection F c)

/-- 概要：元の局所左 Kan 形状上で A の元の Yoneda 図式を固定する。
方針：同じ元の射影だけを宇宙変更して Yoneda へ合成する。
規約：形状は任意の F の slice 引き戻し。使われ方：Hom 前層の局所密度表示。 -/
def homWeightLocalYonedaDiagram {A C : SSet.{u}} [Quasicategory A]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj (leftKanShape F c) ⟶ PresheafInfinity A :=
  (SSet.uliftFunctor.{u + 1, u}).map (leftKanProjection F c) ≫ yonedaInfinityMap A

/-- 概要：元の密度図式の実比較への制限は局所 Yoneda 図式そのもの。
方針：比較の厳密な射影則を持ち上げる。
規約：全図式の等式。使われ方：元の密度全余錐の型の正規化。 -/
lemma homWeightLocalElementsComparison_yoneda
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).map (homWeightLocalElementsComparison F c) ≫
      presheafElementsYonedaDiagram (homWeightPresheaf F c) = homWeightLocalYonedaDiagram F c := by
  rw [presheafElementsYonedaDiagram, ← Category.assoc, ← Functor.map_comp,
    homWeightLocalElementsComparison_projection]
  rfl

/-- 概要：元の Hom 前層の密度全余錐を局所左 Kan 形状へ制限する。
方針：射影を保つ実比較で元の全余錐を制限し、図式の厳密な一致を使う。
規約：元の全余錐写像を保持する。使われ方：Hom 係数族の点ごとの余極限の指定。 -/
def homWeightLocalYonedaCocone
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) : JoinCocone (homWeightLocalYonedaDiagram F c) :=
  let d := (presheafDensityCocone (homWeightPresheaf F c)).restrict
    ((SSet.uliftFunctor.{u + 1, u}).map (homWeightLocalElementsComparison F c))
  ⟨d.val, d.property.trans (homWeightLocalElementsComparison_yoneda F c)⟩

/-- 概要：局所 Yoneda 全余錐の頂点は元の Hom 前層そのもの。
方針：join の制限が右の零単体を固定することと元の密度頂点の式を使う。
規約：頂点の同型ではなく等式。使われ方：Hom 係数族の元の値の回収。 -/
lemma homWeightLocalYonedaCocone_vertex
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    (homWeightLocalYonedaCocone F c).vertex = functorVertex (homWeightPresheaf F c) := by
  rw [JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (joinInr _ _ ≫
    (joinMap ((SSet.uliftFunctor.{u + 1, u}).map (homWeightLocalElementsComparison F c))
      (𝟙 (Δ[0] : SSet.{u + 1})) ≫ (presheafDensityCocone (homWeightPresheaf F c)).val)) = _
  rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
  exact presheafDensityCocone_vertex (homWeightPresheaf F c)

/-- 概要：元の Hom 前層を頂点とする局所 Yoneda 全余錐は余極限。
方針：元の密度余極限を実比較の同値で制限して普遍性を保存する。
規約：F の充満忠実性や C の余完備性は要求しない。
使われ方：指定単位の左 Kan 普遍性を検証するための局所余極限。 -/
lemma homWeightLocalYonedaCocone_isColimit
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) : IsColimitCone (homWeightLocalYonedaCocone F c) := by
  have h := (isColimitCone_iff_restrict_equivalentShape
    ((SSet.uliftFunctor.{u + 1, u}).map (homWeightLocalElementsComparison F c))
    (IsQCatEquivalence.ulift.{u, u + 1}
      (homWeightLocalElementsComparison_isPrecompositionEquivalence F c).isQCatEquivalence)
    (presheafDensityCocone (homWeightPresheaf F c))).mp
      (presheafDensityCocone_isColimit (homWeightPresheaf F c))
  exact (F2.isColimitCone_iff_of_cocone_val_eq
    ((presheafDensityCocone (homWeightPresheaf F c)).restrict
      ((SSet.uliftFunctor.{u + 1, u}).map (homWeightLocalElementsComparison F c)))
    (homWeightLocalYonedaCocone F c) rfl).mp h

end SerrePositivity.InfinityCategories.F2.Presentable
