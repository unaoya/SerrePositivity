module
public import SerrePositivity.KST.Fibration.RelativeSFibrationFiber
public import SerrePositivity.KST.Fibration.RelativeSQuotientRealization

/-! # 相対 S の指定 fiber から、商の元の core S 射の同じ基点上の fiber への実比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の相対基点を実際の商の core S 実現へ送る。 -/
def quotientSFibrationBasepoint
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) : Δ[0] ⟶ coreSRealizationFunctor.obj (sInputModel C) :=
  relativeSFibrationBasepoint h ≫ simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q)

/-- 同じ完全商関手の core S 実現射の、同じ基点上の実 fiber 模型。 -/
def quotientSFibrationFiber
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) : SSet.{u} :=
  homotopyPullbackObject (simplicialDiagonalFunctor.map (coreSExactMap q))
    (quotientSFibrationBasepoint h)

/-- 商の実 fiber の元の左射影。 -/
def quotientSFibrationFiberProjection
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    quotientSFibrationFiber h ⟶ coreSRealizationFunctor.obj (sInputModel B) :=
  pullback.fst _ _

/-- 元の core S(B) と指定した基点を恒等射で保つ、二つの実 fiber の比較。 -/
def relativeToQuotientSFiberMap
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) : relativeSFibrationFiber h ⟶ quotientSFibrationFiber h :=
  homotopyPullbackMap (𝟙 _) (𝟙 _)
    (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q))
    (by rw [relativeSQuotientRealization_core, Category.id_comp])
    (by simp only [Category.id_comp]; rfl)

/-- 実 fiber 比較の後の射影は、元の相対 fiber の同じ射影を回収する。 -/
theorem relativeToQuotientSFiberMap_fst
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    relativeToQuotientSFiberMap h ≫ pullback.fst
        (simplicialDiagonalFunctor.map (coreSExactMap q))
        (AnodyneKanReplacement.factorization.p.app (Arrow.mk (quotientSFibrationBasepoint h))) =
      relativeSFibrationFiberProjection h := by
  unfold relativeToQuotientSFiberMap
  rw [homotopyPullbackMap_fst, Category.comp_id]
  rfl

/-- 商実現比較が局所化同型と証明できれば、構成した同じ実 fiber 比較も局所化同型。
この条件はここでは証明せず、元の商比較の証明課題を正確に保持する。 -/
theorem relativeToQuotientSFiberMap_localized_isIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (hq : IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeToQuotientSFiberMap h)) :=
  homotopyPullbackMap_localized_isIso (𝟙 _) (𝟙 _)
    (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q))
    (by rw [relativeSQuotientRealization_core, Category.id_comp])
    (by simp only [Category.id_comp]; rfl)
    (by infer_instance) (by infer_instance) hq

/-- 未証明の商実現比較を正確に入力したとき、元の包含側と商射の実 fiber は局所化で同型。 -/
def quotientSFibrationFiberIsoOfComparison
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (hq : IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q)))) :
    AnodyneHomotopy.anodyneQ.obj (coreSRealizationFunctor.obj (sInputModel A)) ≅
      AnodyneHomotopy.anodyneQ.obj (quotientSFibrationFiber h) := by
  have := relativeToQuotientSFiberMap_localized_isIso h hq
  exact relativeSFibrationFiberIso h ≪≫
    asIso (AnodyneHomotopy.anodyneQ.map (relativeToQuotientSFiberMap h))

/-- 条件付きの商 fiber 比較でも、元の Verdier 包含の実現射は同じ射影で回収される。 -/
theorem quotientSFibrationFiberIsoOfComparison_hom_projection
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (hq : IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q)))) :
    (quotientSFibrationFiberIsoOfComparison h hq).hom ≫
        AnodyneHomotopy.anodyneQ.map (quotientSFibrationFiberProjection h) =
      AnodyneHomotopy.anodyneQ.map (simplicialDiagonalFunctor.map (coreSExactMap i)) := by
  change ((relativeSFibrationFiberIso h).hom ≫
    AnodyneHomotopy.anodyneQ.map (relativeToQuotientSFiberMap h)) ≫
      AnodyneHomotopy.anodyneQ.map (quotientSFibrationFiberProjection h) = _
  rw [Category.assoc, ← Functor.map_comp]
  have hp : relativeToQuotientSFiberMap h ≫ quotientSFibrationFiberProjection h =
      relativeSFibrationFiberProjection h := relativeToQuotientSFiberMap_fst h
  rw [hp]
  exact relativeSFibrationFiberIso_hom_projection h

end SerrePositivity.KST.Fibration
