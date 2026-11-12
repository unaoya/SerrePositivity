module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VariableSourcePrismUniversal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary

/-!
概要：二端点と底を同時に指定する prism の相対内部 Hom のデータ。
方針：区間境界の二射の図式を係数ごとに貼り合わせる。
規約：端点と底の条件は射の厳密な等式。
使われ方：全 lift prism の同時端点制限の left fibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 概要：区間境界の二射の図式は標的の射との合成に自然。
方針：同じ端点による二つの分岐で確認する。
規約：単体集合は任意。
使われ方：境界の図式の底への射の確認。 -/
lemma intervalBoundaryDiagram_postcomp {A E B : SSet.{u}} (f g : A ⟶ E) (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (f ≫ p) (g ≫ p) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  ext x
  change p.app _ (if x.1.val 0 = 0 then f.app _ x.2 else g.app _ x.2) =
    (if x.1.val 0 = 0 then (f ≫ p).app _ x.2 else (g ≫ p).app _ x.2)
  split <;> rfl

/-- 概要：二端点と底の prism の族を相対内部 Hom のデータに束ねる。
方針：二端点の図式を curry し、底の境界との一致を確認する。
規約：係数とパラメーターの両方に依存する端点を許す。
使われ方：同時端点制限の相対ホーン充填の下の射。 -/
def prismBoundaryData {E B K L : SSet.{u}} (p : E ⟶ B)
    (r : internalHom.PullbackObjObj ((boundary 1).ι ▷ K) p)
    (v₀ v₁ : K ⊗ L ⟶ E) (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B)
    (h₀ : v₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ)
    (h₁ : v₁ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ δ) : L ⟶ r.pt := by
  refine r.isPullback.lift (curry ((α_ (boundary 1 : SSet.{u}) K L).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram v₀ v₁)) (curry ((α_ Δ[1] K L).hom ≫ δ)) ?_
  change curry _ ≫ (ihom ((boundary 1 : SSet.{u}) ⊗ K)).map p =
    curry _ ≫ (pre ((boundary 1).ι ▷ K)).app B
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_pre_app, uncurry_curry, uncurry_curry]
  change (α_ (boundary 1 : SSet.{u}) K L).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram v₀ v₁ ≫ p =
    (α_ (boundary 1 : SSet.{u}) K L).hom ≫ ((boundary 1).ι ▷ (K ⊗ L)) ≫ δ
  rw [intervalBoundaryDiagram_postcomp, h₀, h₁, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict]

/-- 概要：境界データの第一射影は指定した二端点の curry。
方針：引き戻しの持ち上げの第一射影を取る。
規約：二端点を一つの境界図式として保持する。
使われ方：充填後の両端の回収。 -/
lemma prismBoundaryData_fst {E B K L : SSet.{u}} (p : E ⟶ B)
    (r : internalHom.PullbackObjObj ((boundary 1).ι ▷ K) p)
    (v₀ v₁ : K ⊗ L ⟶ E) (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B)
    (h₀ : v₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ)
    (h₁ : v₁ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ δ) :
    prismBoundaryData p r v₀ v₁ δ h₀ h₁ ≫ r.fst =
      curry ((α_ (boundary 1 : SSet.{u}) K L).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram v₀ v₁) :=
  r.isPullback.lift_fst _ _ _

/-- 概要：境界データの第二射影は指定した底の curry。
方針：引き戻しの持ち上げの第二射影を取る。
規約：底の prism 全体を保持する。
使われ方：充填後の底の回収。 -/
lemma prismBoundaryData_snd {E B K L : SSet.{u}} (p : E ⟶ B)
    (r : internalHom.PullbackObjObj ((boundary 1).ι ▷ K) p)
    (v₀ v₁ : K ⊗ L ⟶ E) (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B)
    (h₀ : v₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ)
    (h₁ : v₁ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ δ) :
    prismBoundaryData p r v₀ v₁ δ h₀ h₁ ≫ r.snd = curry ((α_ Δ[1] K L).hom ≫ δ) :=
  r.isPullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
