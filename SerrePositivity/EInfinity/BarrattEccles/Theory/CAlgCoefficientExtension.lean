module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.AlgebraCoefficientExtension
public import SerrePositivity.EInfinity.BarrattEccles.CAlgForgetDerived
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.WeakNerveInverts
public import SerrePositivity.HomotopicalAlgebra.Quillen.Brown
public import SerrePositivity.HomotopicalAlgebra.Quillen.CofibrantObjects

/-!
# Barratt–Eccles の導来係数拡大

## 概要
HA §3.2.2 の底変更を、具体的な転送モデル構造から構成する。

## 方針
係数制限が fibration と弱同値を保つので、厳密拡大は左 Quillen。
cofibrant な代数への適用を、既存の局所化に沿って延長する。

## 規約
任意の環準同型を許し、転送モデル構造は証明で局所的に選ぶ。

## 使われ方
M13 の導来底変更関手。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory SSet _root_.HomotopicalAlgebra _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories SerrePositivity.Quillen
open scoped Simplicial

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 項別係数制限は全射と擬同型を保つので右 Quillen。 -/
lemma coefficientRestriction_isRightQuillen :
    let := modelCategory S
    let := modelCategory T
    IsRightQuillen (coefficientRestriction f) := by
  let := modelCategory S
  let := modelCategory T
  have hf {X Y : (operad T).Algebra} (g : X ⟶ Y) (h : (fibrations _ ) g) :
      (fibrations _) ((coefficientRestriction f).map g) := by
    apply (_root_.HomotopicalAlgebra.fibration_iff _).mp
    apply (fibration_iff S _).mpr
    exact (fibration_iff T g).mp ((_root_.HomotopicalAlgebra.fibration_iff g).mpr h)
  refine ⟨fun _ _ g hg => hf g hg, ?_⟩
  intro X Y g hg
  refine ⟨hf g hg.1, ?_⟩
  apply (_root_.HomotopicalAlgebra.weakEquivalence_iff _).mp
  apply (weakEquivalence_iff S _).mpr
  apply coefficientRestriction_map_quasiIso
  exact (weakEquivalence_iff T g).mp ((_root_.HomotopicalAlgebra.weakEquivalence_iff g).mpr hg.2)

/-- 厳密拡大は、同じ環準同型に沿う係数制限の左 Quillen 随伴。 -/
lemma coefficientExtension_isLeftQuillen :
    let := modelCategory S
    let := modelCategory T
    IsLeftQuillen (coefficientExtension f) := by
  let := modelCategory S
  let := modelCategory T
  let _ := coefficientRestriction_isRightQuillen f
  exact isLeftQuillen_of_isRightQuillen (coefficientAlgebraAdjunction f)

/-- 厳密拡大は cofibrant な代数を cofibrant な代数に送る。 -/
def cofibrantAlgebraCoefficientExtension : CofibrantAlgebra S ⥤ CofibrantAlgebra T := by
  let := modelCategory S
  let := modelCategory T
  letI := (coefficientAlgebraAdjunction f).isLeftAdjoint
  letI := coefficientExtension_isLeftQuillen f
  refine ObjectProperty.lift _ (cofibrantAlgebraInclusion S ⋙ coefficientExtension f) ?_
  intro X
  let hX := cofibrantAlgebra_isCofibrant S X
  exact isCofibrant_obj (coefficientExtension f) ((cofibrantAlgebraInclusion S).obj X)

/-- DK 入力での拡大。Hom の ULift だけを追加する。 -/
def cofibrantAlgebraDKCoefficientExtension :
    (cofibrantAlgebraRelativeCategory S).category ⥤
      (cofibrantAlgebraRelativeCategory T).category :=
  (ULiftHom.down.{u, u + 1, u + 1} (C := CofibrantAlgebra S)) ⋙
    cofibrantAlgebraCoefficientExtension f ⋙
    (ULiftHom.up.{u, u + 1, u + 1} (C := CofibrantAlgebra T))

/-- DK 入力間の係数拡大は指定の擬同型を保つ。 -/
lemma cofibrantAlgebraDKCoefficientExtension_map_weak
    {X Y : (cofibrantAlgebraRelativeCategory S).category} (g : X ⟶ Y)
    (hg : (cofibrantAlgebraRelativeCategory S).weakEquivalences g) :
    (cofibrantAlgebraRelativeCategory T).weakEquivalences
      ((cofibrantAlgebraDKCoefficientExtension f).map g) := by
  let := modelCategory S
  let := modelCategory T
  let hL := coefficientExtension_isLeftQuillen f
  let k := (cofibrantAlgebraDKInclusion S).map g
  let hX : IsCofibrant ((cofibrantAlgebraDKInclusion S).obj X) :=
    cofibrantAlgebra_isCofibrant S X
  let hY : IsCofibrant ((cofibrantAlgebraDKInclusion S).obj Y) :=
    cofibrantAlgebra_isCofibrant S Y
  let hk : WeakEquivalence k := (weakEquivalence_iff S k).mpr
    ((cofibrantAlgebraRelativeCategory_weakEquivalences_iff S g).mp hg)
  apply (cofibrantAlgebraRelativeCategory_weakEquivalences_iff T _).mpr
  exact (weakEquivalence_iff T _).mp (map_weakEquivalence_of_cofibrant (coefficientExtension f) k)

/-- 拡大後の局所化は、拡大前の cofibrant 代数の擬同型を反転する。 -/
lemma cAlgCoefficientExtensionSource_inverts :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (nerveMap (cofibrantAlgebraDKCoefficientExtension f) ≫ cAlgLocalizationSource T)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (cofibrantAlgebraRelativeCategory S)) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges_inverts_of_arrows
  intro X Y g hg
  let F := cofibrantAlgebraDKCoefficientExtension f
  have h := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges_inverts_arrows (cofibrantAlgebraRelativeCategory T) _
    (cAlgLocalizationSource_inverts T) (F.map g)
    (cofibrantAlgebraDKCoefficientExtension_map_weak f g hg)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := ((nerve.edgeMk g).map (nerveMap F ≫ cAlgLocalizationSource T)).toTruncated)
    (f := ((nerve.edgeMk (F.map g)).map (cAlgLocalizationSource T)).toTruncated) ?_).mpr h
  change (cAlgLocalizationSource T).app (Opposite.op ⦋1⦌)
    ((nerveMap F).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ g)) =
      (cAlgLocalizationSource T).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ (F.map g))
  rw [nerveMap_app_mk₁]

/-- HA §3.2.2 の底変更関手を、厳密な係数拡大から延長する。 -/
lemma cAlgCoefficientExtension_exists :
    ∃ L : CAlg_R S ⟶ CAlg_R T,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cAlgLocalizationSource S ≫ L)
        (nerveMap (cofibrantAlgebraDKCoefficientExtension f) ≫ cAlgLocalizationSource T)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.localization_extension_exists (cAlgLocalizationSource S)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (cofibrantAlgebraRelativeCategory S)) (cAlgLocalizationSource_inverts S)
    (cAlgLocalizationPrecomposition_isQCatEquivalence S (CAlg_R T)) _
    (cAlgCoefficientExtensionSource_inverts f)

/-- 厳密な拡大を cofibrant 入力に施して得る導来係数拡大。 -/
def barrattEcclesBaseChange : CAlg_R S ⟶ CAlg_R T :=
  (cAlgCoefficientExtension_exists f).choose

/-- 導来係数拡大は cofibrant 入力上で厳密な拡大と自然に一致する。 -/
def barrattEcclesBaseChange_cofibrantIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cAlgLocalizationSource S ≫ barrattEcclesBaseChange f)
      (nerveMap (cofibrantAlgebraDKCoefficientExtension f) ≫ cAlgLocalizationSource T) :=
  (cAlgCoefficientExtension_exists f).choose_spec.some

end SerrePositivity.EInfinity.BarrattEccles
